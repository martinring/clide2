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

case class SessionInfo(
    id: Option[Long] = None,
    user: String,
    project: Long,
    active: Boolean)
    
/* Json (de)serialization */
object SessionInfo { implicit val json = Json.format[SessionInfo] }

object SessionInfos extends Table[SessionInfo]("projects") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def userName     = column[String]("name")
  def projectId    = column[Long]("project")
  def active       = column[Boolean]("active")
  def *            = id.? ~ userName ~ projectId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _)
   
  def autoinc = id.? ~ userName ~ projectId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _) returning id
}