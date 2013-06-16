package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

case class Project(id: Int, name: String, ownerId: Int)

object Projects extends Table[Project]("projects") {
  def id      = column[Int]("id", O.PrimaryKey, O.AutoInc)
  def name    = column[String]("name")
  def ownerId = column[Int]("owner")
  def owner   = foreignKey("fk_project_user", ownerId, Users)(_.id)
  def *       = id ~ name ~ ownerId <> (Project, Project.unapply _)
}

object Rights extends Table[(Int,Int,Boolean,Boolean)]("rights") {
  def projectId = column[Int]("project")
  def userId    = column[Int]("user")
  def project   = foreignKey("fk_right_project", projectId, Projects)(_.id)
  def user      = foreignKey("fk_right_user", userId, Users)(_.id)
  def pk        = primaryKey("pk_right", (projectId,userId))
  def read      = column[Boolean]("read")
  def write     = column[Boolean]("write")
  def *         = projectId ~ userId ~ read ~ write
}