package clide.persistence

import clide.models._
import scala.slick.lifted.ForeignKeyAction

trait ProjectTables { this: Profile with Mappers with UserTables with FileTables =>
  import profile.simple._
 
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
    
    def delete(id: Long)(implicit session: Session) = 
      Query(ProjectInfos).filter(_.id === id).delete

    def delete(p: ProjectInfo)(implicit session: Session) =
      Query(ProjectInfos).filter(_.id === p.id).delete
    
    def update(p: ProjectInfo)(implicit session: Session) = 
      Query(ProjectInfos).filter(_.id === p.id).update(p)        
    
    def getByOwner(owner: String)(implicit session: Session) =
      Query(ProjectInfos).filter(_.ownerName === owner).elements      
    
    def get(owner: String, name: String)(implicit session: Session) =
      Query(ProjectInfos).filter(_.ownerName === owner)
                         .filter(_.name === name).elements
      
    def get(id: Long)(implicit session: Session) =
      Query(ProjectInfos).filter(_.id === id).firstOption
  }
    
  object ProjectAccessLevels extends Table[(Long,String,ProjectAccessLevel.Value)]("rights") {    
    def projectId = column[Long]("project")
    def userName  = column[String]("user")
    def project   = foreignKey("fk_right_project", projectId, ProjectInfos)(_.id, 
        onUpdate = ForeignKeyAction.Cascade, 
        onDelete = ForeignKeyAction.Cascade)
    def user      = foreignKey("fk_right_user", userName, UserInfos)(_.name, 
        onUpdate = ForeignKeyAction.Cascade, 
        onDelete = ForeignKeyAction.Cascade)
    def pk        = primaryKey("pk_right", (projectId,userName))
    def level     = column[ProjectAccessLevel.Value]("policy")  
    def *         = projectId ~ userName ~ level
    
    def change(project: Long, user: String, level: ProjectAccessLevel.Value)(implicit session: Session) = {
      level match {
        case ProjectAccessLevel.None =>
          Query(ProjectAccessLevels).filter(l => l.projectId === project && l.userName === user).delete
        case level => // TODO: Transaction?
          val q = Query(ProjectAccessLevels).filter(l => l.projectId === project && l.userName === user) 
          q.firstOption match {
            case None          => ProjectAccessLevels.insert((project,user,level))
            case Some((p,u,l)) => q.update((p,u,level)) 
          }
      }
    }
    
    def getUserProjects(user: String)(implicit session: Session) =
      Query(ProjectAccessLevels).filter(_.userName === user)
                                .join(Query(ProjectInfos)).on(_.userName === _.name)
                                .map{ case (a,p) => p -> a.level }.elements
    
    def getProjectUsers(project: Long)(implicit session: Session) = 
      Query(ProjectAccessLevels).filter(_.projectId === project).elements
  }
  
  object SessionInfos extends Table[SessionInfo]("sessions") {
    def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def userName     = column[String]("name")
    def color        = column[String]("color")
    def projectId    = column[Long]("project")
    def activeFileId = column[Option[Long]]("activeFile")
    def active       = column[Boolean]("active")
    def activeFile   = foreignKey("fk_session_file", activeFileId, FileInfos)(_.id,
        onUpdate = ForeignKeyAction.SetNull, 
        onDelete = ForeignKeyAction.SetNull)
    def user         = foreignKey("fk_session_user", userName, UserInfos)(_.name, 
        onUpdate = ForeignKeyAction.Cascade, 
        onDelete = ForeignKeyAction.Cascade)
    def project      = foreignKey("fk_session_project", projectId, ProjectInfos)(_.id, 
        onUpdate = ForeignKeyAction.Cascade, 
        onDelete = ForeignKeyAction.Cascade)
        
    def * = id ~ userName ~ color ~ projectId ~ activeFileId ~ active <> (SessionInfo.apply _, SessionInfo.unapply _)     
    
    def create(user: String, color: String, project: Long, activeFile: Option[Long], active: Boolean)(implicit session: Session) = {
      val q = this.id.? ~ this.userName ~ this.color ~ this.projectId ~ this.activeFileId ~ this.active returning this.id
      val id = q.insert((None,user,color,project,activeFile,active))
      SessionInfo(id,user,color,project,activeFile,active)
    }
    
    def update(info: SessionInfo)(implicit session: Session) = {
      val q = for (i <- SessionInfos if i.id === info.id) yield i
      q.update(info)
    }
    
    def delete(info: SessionInfo)(implicit session: Session) = {
      val q = for (i <- SessionInfos if i.id === info.id) yield i
      q.delete
    }
    
    def get(id: Long)(implicit session: Session) = {
      val q = for (i <- SessionInfos if i.id === id) yield i
      q.firstOption
    }
    
    def getForProject(id: Long)(implicit session: Session) = {
      val q = for (i <- SessionInfos if i.projectId === id) yield i
      q.elements
    }
   
    def getForUser(name: String)(implicit session: Session) = {
      val q = for (i <- SessionInfos if i.userName === name) yield i
      q.elements
    }  
  }
}