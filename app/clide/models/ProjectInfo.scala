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

case class ProjectInfo(
    id: Long,
    name: String,
    owner: String,
    description: Option[String] = None) {
  lazy val root = f"files/$owner/$name" // TODO: This should be configured in the future  
}
/* Json (de)serialization */
object ProjectInfo { implicit val json = Json.format[ProjectInfo] }

object ProjectInfos extends Table[ProjectInfo]("projects") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def ownerName    = column[String]("owner")
  def description  = column[Option[String]]("description")
  def owner        = foreignKey("fk_project_user", ownerName, UserInfos)(_.name, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
  def *            = id ~ name ~ ownerName ~ description <> (ProjectInfo.apply _, ProjectInfo.unapply _)
  
  // for every owner, the names of all his projects must be unique
  // which means, that project names alone don't have to be.
  def ownerProject = index("idx_owner_project", (ownerName, name), unique = true)    
  
  def create(name: String, owner: String, description: Option[String])(implicit session: Session) = { 
    val q = (this.id.? ~ this.name ~ this.ownerName ~ this.description returning this.id)
    val id = q.insert((None,name,owner,description))
    ProjectInfo(id,name,owner,description)
  }
  
  def delete(id: Long)(implicit session: Session) = get(id).delete
  
  def update(p: ProjectInfo)(implicit session: Session) = get(p.id).update(p)
      
  def byOwner(owner: String) = 	
    for(project <- ProjectInfos if project.ownerName === owner)
      yield project
  
  def byOwnerAndName(owner: String, name: String) =
    for(project <- byOwner(owner) if project.name === name)
      yield project
  
  def getByOwner(owner: String)(implicit session: Session) = 
    byOwner(owner).elements  
  
  def get(owner: String, name: String)(implicit session: Session) =
    byOwnerAndName(owner,name).firstOption
    
  def get(id: Long) =
    for (project <- ProjectInfos if project.id === id) yield project
    
  
}