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
    id: Long,
    user: String,
    color: String,
    project: Long,
    activeFile: Option[Long],    
    active: Boolean) {
  override def equals(other: Any) = other match {
    case SessionInfo(id,_,_,_,_,_) => id == this.id
    case _ => false
  }
}
    
/* Json (de)serialization */
object SessionInfo { implicit val json = Json.format[SessionInfo] }

object SessionInfos extends Table[SessionInfo]("sessions") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def userName     = column[String]("name")
  def color        = column[String]("color")
  def projectId    = column[Long]("project")
  def activeFileId = column[Option[Long]]("activeFile")
  def active       = column[Boolean]("active")
  def activeFile   = foreignKey("fk_session_file", activeFileId, FileInfos)(_.id,
      onUpdate = ForeignKeyAction.SetNull, 
      onDelete = ForeignKeyAction.SetNull)
  def user         = foreignKey("fk_session_user", userName, UserInfos)(_.name, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def project      = foreignKey("fk_session_project", projectId, ProjectInfos)(_.id, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
      
  def * = id ~ userName ~ color ~ projectId ~ activeFileId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _)     
  
  def create(user: String, color: String, project: Long, activeFile: Option[Long], active: Boolean)(implicit session: Session) = {
    val q = this.id.? ~ this.userName ~ this.color ~ this.projectId ~ this.activeFileId ~ this.active returning this.id
    val id = q.insert((None,user,color,project,activeFile,active))
    SessionInfo(id,user,color,project,activeFile,active)
  }
  
  def update(info: SessionInfo)(implicit session: Session) = {
    val q = for (i <- SessionInfos if i.id === info.id) yield i
    q.update(info)
  }
  
  def delete(info: SessionInfo)(implicit session: Session) = {
    val q = for (i <- SessionInfos if i.id === info.id) yield i
    q.delete
  }
  
  def get(id: Long)(implicit session: Session) = {
    val q = for (i <- SessionInfos if i.id === id) yield i
    q.firstOption
  }
  
  def getForProject(id: Long)(implicit session: Session) = {
    val q = for (i <- SessionInfos if i.projectId === id) yield i
    q.elements
  }
 
  def getForUser(name: String)(implicit session: Session) = {
    val q = for (i <- SessionInfos if i.userName === name) yield i
    q.elements
  }  
}