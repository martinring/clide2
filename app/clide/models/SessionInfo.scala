package clide.models

import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID
import java.io.File
import play.api.Play
import clide.web.controllers.Projects
import scala.slick.lifted.ForeignKeyAction

case class SessionInfo(
    id: Option[Long] = None,
    user: String,
    project: Long,
    active: Boolean) {
  override def equals(other: Any) = other match {
    case SessionInfo(id@Some(_),_,_,_) => id == this.id
    case _ => false
  }
}
    
/* Json (de)serialization */
object SessionInfo { implicit val json = Json.format[SessionInfo] }

object SessionInfos extends Table[SessionInfo]("sessions") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def userName     = column[String]("name")
  def projectId    = column[Long]("project")
  def active       = column[Boolean]("active")
  def user         = foreignKey("ky_session_user", userName, UserInfos)(_.name, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def project      = foreignKey("fk_session_project", projectId, ProjectInfos)(_.id, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def *            = id.? ~ userName ~ projectId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _)
   
  def autoinc = id.? ~ userName ~ projectId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _) returning id
}