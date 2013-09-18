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
  
object OpenFiles extends Table[(Long,Long)]("openFiles") {
  implicit val pathMapper = MappedTypeMapper.base[Seq[String], String](
      _.mkString("/") , _.split('/').toSeq.filter(!_.isEmpty()))
    
  def sessionId   = column[Long]("session")
  def fileId      = column[Long]("file")  
  
  def session = foreignKey("fk_openFile_session", sessionId, SessionInfos)(_.id,
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def file = foreignKey("fk_openFile_file", fileId, FileInfos)(_.id,
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def pk = primaryKey("pk_openFile", (sessionId,fileId))
        
  def * = sessionId ~ fileId
    
  def get(sessionId: Long) = for {
    openFile <- OpenFiles if openFile.sessionId === sessionId
    file <- openFile.file
  } yield file  
}