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
  path: String,
  deleted: Boolean,
  exists: Boolean,
  isDirectory: Boolean,
  parent: Option[Long])

object FileInfos extends Table[FileInfo]("openFiles") {
  def id          = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def projectId   = column[Long]("projectId")  
  def path        = column[String]("path")
  def deleted     = column[Boolean]("deleted")
  def exists      = column[Boolean]("exists")
  def isDirectory = column[Boolean]("isDirectory")
  def parentId    = column[Option[Long]]("parent")
      
  def project     = foreignKey("fk_fileInfos_project", projectId, ProjectInfos)(_.id, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
      
  def parent      = foreignKey("fk_fileInfos_parent", parentId, FileInfos)(_.id, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  
  def projectPath = index("project_path", (projectId,path), unique = true)
  
  def *        = id ~ projectId ~ path ~ deleted ~ exists ~ isDirectory ~ parentId <> (FileInfo.apply _, FileInfo.unapply _)
  
  def create(project: Long, path: String, deleted: Boolean, exists: Boolean, isDirectory: Boolean, parent: Option[Long])(implicit session: Session) = {
    val autoinc = this.id.? ~ this.projectId ~ this.path ~ this.deleted ~ this.exists ~ this.isDirectory ~ this.parentId returning this.id    
    val id = autoinc.insert((None,project,path,deleted,exists,isDirectory,parent))
    FileInfo(id,project,path,deleted,exists,isDirectory,parent)
  }  
  
  def get(project: ProjectInfo, path: String) = for {
    file <- FileInfos if file.projectId === project.id && file.path === path  
  } yield file
  
  def get(id: Long) = for {
    file <- FileInfos if file.id === id
  } yield file
  
  def getChildren(file: FileInfo) = for {
    file <- FileInfos if file.parentId === file.id
  } yield file
}