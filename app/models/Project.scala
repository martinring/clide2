package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

case class Project(id: Int, name: String, ownerName: String)

object Projects extends Table[Project]("projects") {
  def id      = column[Int]("id", O.PrimaryKey, O.AutoInc)
  def name    = column[String]("name")
  def ownerName = column[String]("owner")
  def owner   = foreignKey("fk_project_user", ownerName, Users)(_.name)
  def *       = id ~ name ~ ownerName <> (Project, Project.unapply _)
}

object Rights extends Table[(Int,String,Boolean,Boolean)]("rights") {
  def projectId = column[Int]("project")
  def userName  = column[String]("user")
  def project   = foreignKey("fk_right_project", projectId, Projects)(_.id)
  def user      = foreignKey("fk_right_user", userName, Users)(_.name)
  def pk        = primaryKey("pk_right", (projectId,userName))
  def read      = column[Boolean]("read")
  def write     = column[Boolean]("write")
  def *         = projectId ~ userName ~ read ~ write
}