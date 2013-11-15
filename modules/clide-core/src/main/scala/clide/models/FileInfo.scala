package clide.models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import akka.actor.Actor
import java.sql.Date
import scala.slick.lifted.ForeignKeyAction

case class FileInfo(
  id: Long,
  project: Long,
  path: Seq[String],
  mimeType: Option[String],
  deleted: Boolean,
  exists: Boolean,
  isDirectory: Boolean,
  parent: Option[Long]) {
  override def equals(other: Any) = other match {
    case f: FileInfo if f.id == this.id => true
    case _ => false
  }
}