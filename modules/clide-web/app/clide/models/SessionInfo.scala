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