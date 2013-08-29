package models

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json._

case class Folder(id: Option[Long], name: String, parent: Option[Long]) {
  def toJsonTree(implicit session: Session): JsObject = Json.obj(
    "id" -> id,
    "name" -> name,
    "parent" -> parent,
    "files" -> JsArray(Folders.getSubfolders(id.get).toSeq.map(_.toJsonTree)))
}
object Folder { implicit val format = Json.format[Folder] }

object Folders extends Table[Folder]("folders") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def parentId     = column[Option[Long]]("parent")
  def parent       = foreignKey("fk_folder_parent", parentId, Folders)(_.id)
  
  def parentName   = index("idx_parent_name", (parentId, name), unique = true) 
  
  def * = id.? ~ name ~ parentId <> (Folder.apply _ , Folder.unapply _)
  def autoinc = id.? ~ name ~ parentId <> (Folder.apply _ , Folder.unapply _) returning id
  
  def get(id: Long)(implicit session: Session) = 
    (for(f <- Folders if f.id === id) yield f.*).firstOption
    
  def getSubfolders(id: Long)(implicit session: Session) =
    (for(f <- Folders if f.parentId === id) yield f.*).elements
  
  def create(folder: Folder)(implicit session: Session) = {  
    val id = autoinc.insert(folder)
    // Create Directory
    folder.copy(id=Some(id)) 
  }
}