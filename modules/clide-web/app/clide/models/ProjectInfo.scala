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
import scala.slick.lifted.ForeignKeyAction

case class ProjectInfo(
    id: Long,
    name: String,
    owner: String,
    description: Option[String] = None) {
  lazy val root = f"files/$owner/$name" // TODO: This should be configured in the future  
}
/* Json (de)serialization */
object ProjectInfo { implicit val json = Json.format[ProjectInfo] }