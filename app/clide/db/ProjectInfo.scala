package clide.db

import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID
import java.io.File
import play.api.Play

case class ProjectInfo(
    id: Option[Long], 
    name: String, 
    owner: String, 
    description: Option[String] = None) {
  lazy val root = f"files/$owner/$name"
  lazy val uniqueName = f"$owner/$name"
}
/* Json (de)serialization */
object ProjectInfo { implicit val json = Json.format[ProjectInfo] }

object Projects extends Table[ProjectInfo]("projects") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def ownerName    = column[String]("owner")
  def description  = column[Option[String]]("description")
  def owner        = foreignKey("fk_project_user", ownerName, Users)(_.name)  
  def *            = id.? ~ name ~ ownerName ~ description <> (ProjectInfo.apply _, ProjectInfo.unapply _)
  
  // for every owner, the names of all his projects must be unique
  // which means, that project names alone don't have to be.
  def ownerProject = index("idx_owner_project", (ownerName, name), unique = true) 
  def autoinc = id.? ~ name ~ ownerName ~ description <> (ProjectInfo.apply _, ProjectInfo.unapply _) returning id
  
  def byOwner(owner: String) = 	
    for(project <- Projects if project.ownerName === owner)
      yield project
  
  def byOwnerAndName(owner: String, name: String) =
    for(project <- byOwner(owner) if project.name === name)
      yield project
  
  def getByOwner(owner: String)(implicit session: Session) = 
    byOwner(owner).elements  
  
  def get(owner: String, name: String)(implicit session: Session) =
    byOwnerAndName(owner,name).firstOption
    
  def create(project: ProjectInfo)(implicit session: Session) = {    
    Play.getFile(project.root).mkdirs()
    val id = autoinc.insert(project)
    project.copy(id=Some(id))
  }
}

object Rights extends Table[(Long,String,Int)]("rights") {  
  def projectId = column[Long]("project")
  def userName  = column[String]("user")
  def project   = foreignKey("fk_right_project", projectId, Projects)(_.id)
  def user      = foreignKey("fk_right_user", userName, Users)(_.name)
  def pk        = primaryKey("pk_right", (projectId,userName))
  def policy    = column[Int]("policy")  
  def *         = projectId ~ userName ~ policy
  
  val None = 0
  val Read = 1
  val Write = 2
  val Admin = 3
}