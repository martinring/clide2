package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import play.api.libs.Crypto
import java.sql.Date
import play.api.libs.json._

case class OpenFile(
    id: Option[Long],
    project: Long,
    path: String)
    
object OpenFiles extends Table[OpenFile]("openFiles") {  
  def id        = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def projectId = column[Long]("projectId")
  def path      = column[String]("path")
  
  def project   = foreignKey("fk_openFile_project", projectId, Projects)(_.id)
  
  def projectPath = index("project_path", (projectId,path), unique = true)
  
  def *        = id.? ~ projectId ~ path <> (OpenFile.apply _, OpenFile.unapply _)
  
  def autoinc  = id.? ~ projectId ~ path <> (OpenFile.apply _, OpenFile.unapply _) returning id
  
  def get(project: ProjectInfo, path: String) = for {
    file <- OpenFiles if file.projectId === project.id && file.path === path  
  } yield *   
}

