package clide.models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import play.api.libs.Crypto
import java.sql.Date
import play.api.libs.json._

case class Revision(file: Long, id: Long, content: String)

object Revisions extends Table[Revision]("revisions") {
  def fileId  = column[Long]("fileId")
  def id      = column[Long]("id")
  def content = column[String]("content")
  
  def file = foreignKey("fk_revision_file", fileId, FileInfos)(_.id)
  
  def fileRevision = index("file_revision", (fileId,id), unique = true)
  
  def * = fileId ~ id ~ content <> (Revision,Revision.unapply _)
  
  def get(file: Long) = for {    
    rev <- Revisions if rev.fileId === file 
  } yield *
}