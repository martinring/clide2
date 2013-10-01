package clide.models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import play.api.libs.Crypto
import java.sql.Date
import play.api.libs.json._
import scala.slick.lifted.ForeignKeyAction

case class FileInfo(
  id: Long,
  project: Long,
  path: Seq[String],
  mimeType: Option[String],
  deleted: Boolean,
  exists: Boolean,
  isDirectory: Boolean,
  parent: Option[Long])
  
object FileInfo {
  implicit val writes = new Writes[FileInfo] {
    def writes(f: FileInfo) = Json.obj(
        "id" -> f.id,
        "name" -> f.path.lastOption,
        "project" -> f.project,
        "path" -> f.path,
        "mimeType" -> f.mimeType,
        "deleted" -> f.deleted,
        "exists" -> f.exists,
        "isDirectory" -> f.isDirectory,
        "parent" -> f.parent)
  }
}