package models

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json.Json

case class Folder(id: Option[Long], name: String, parent: Option[Long])
object Folder { implicit def format = Json.format[Folder] }

object Folders extends Table[Folder]("folders") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def parentId     = column[Option[Long]]("parent")
  def parent       = foreignKey("fk_folder_parent", parentId, Folders)(_.id)
  
  def * = id.? ~ name ~ parentId <> (Folder.apply _ , Folder.unapply _)
  def autoinc = id.? ~ name ~ parentId <> (Folder.apply _ , Folder.unapply _) returning id
  
  def create(folder: Folder)(implicit session: Session) = {  
    val id = autoinc.insert(folder)
    // Create Directory
    folder.copy(id=Some(id)) 
  }
}