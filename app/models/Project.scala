package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.json._
import play.api.libs.functional.syntax._

case class Project(id: Long, name: String, ownerName: String)
/* Json (de)serialization */
object Project { implicit val json = Json.format[Project] }

object Projects extends Table[Project]("projects") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def ownerName    = column[String]("owner")  
  def owner        = foreignKey("fk_project_user", ownerName, Users)(_.name)  
  def *            = id ~ name ~ ownerName <> (Project.apply _, Project.unapply _)
 
  def getForOwner = for {
    name <- Parameters[String]
    projects <- Projects if projects.ownerName === name
  } yield projects
}

object Rights extends Table[(Long,String,Boolean,Boolean)]("rights") {
  def projectId = column[Long]("project")
  def userName  = column[String]("user")
  def project   = foreignKey("fk_right_project", projectId, Projects)(_.id)
  def user      = foreignKey("fk_right_user", userName, Users)(_.name)
  def pk        = primaryKey("pk_right", (projectId,userName))
  def read      = column[Boolean]("read")
  def write     = column[Boolean]("write")
  def *         = projectId ~ userName ~ read ~ write
}