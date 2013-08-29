package models

import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json._

case class Project(
    id: Option[Long], 
    name: String, 
    owner: String, 
    root: Option[Long], 
    description: Option[String] = None)
/* Json (de)serialization */
object Project { implicit val json = Json.format[Project] }

object Projects extends Table[Project]("projects") {
  def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
  def name         = column[String]("name")
  def ownerName    = column[String]("owner")
  def root         = column[Long]("root")
  def description  = column[Option[String]]("description")
  def owner        = foreignKey("fk_project_user", ownerName, Users)(_.name)
  def rootFolder   = foreignKey("fk_project_folder", root, Folders)(_.id)
  def *            = id.? ~ name ~ ownerName ~ root.? ~ description <> (Project.apply _, Project.unapply _)
  
  // for every owner, the names of all his projects must be unique
  // which means, that project names alone don't have to be.
  def ownerProject = index("idx_owner_project", (ownerName, name), unique = true) 
  def autoinc = id.? ~ name ~ ownerName ~ root.? ~ description <> (Project.apply _, Project.unapply _) returning id
  
  val forOwner = for {
	name <- Parameters[String]
    projects <- Projects if projects.ownerName === name
  } yield projects 
  
  def getForOwner(owner: String) = DB.withSession { implicit session: Session =>
    forOwner(owner).elements
  }
    
  def create(project: Project)(implicit session: Session) = {
    val folder = Folders.create(Folder(None,project.name,None))    
    val id = autoinc.insert(project.copy(root = folder.id))
    // Create Directory
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