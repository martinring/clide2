package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.json.Json

case class Folder(id: Long, name: String, parent: Long)
object Folder { implicit def format = Json.format[Folder] }

object Folders extends Table[Folder]("folders") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def parent       = column[Long]("parent")
  
  def * = id ~ name ~ parent <> (Folder.apply _ , Folder.unapply _)
}