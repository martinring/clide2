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
import clide.collaboration.Operation

case class Revision(file: Long, id: Long, op: Operation)

object Revisions extends Table[Revision]("revisions") {
  implicit val opMapper = MappedTypeMapper.base[Operation, String](
    Operation.SourceOperationFormat.writes(_).toString , s => Operation.SourceOperationFormat.reads(Json.parse(s)).get)
    
  def fileId  = column[Long]("fileId")
  def id      = column[Long]("id")
  def content = column[Operation]("content")
  
  def file = foreignKey("fk_revision_file", fileId, FileInfos)(_.id, 
      onUpdate = ForeignKeyAction.Cascade,
      onDelete = ForeignKeyAction.Cascade)
  
  def fileRevision = index("file_revision", (fileId,id), unique = true)
  
  def * = fileId ~ id ~ content <> (Revision,Revision.unapply _)
  
  def get(file: Long)(implicit session: Session) = 
    Query(Revisions).filter(_.fileId === file)
                    .sortBy(_.id.asc)
                    .map(_.content)
                    .elements    
  
  def clear(file: Long)(implicit session: Session) = 
    Query(Revisions).filter(_.fileId === file)
                    .delete    
}