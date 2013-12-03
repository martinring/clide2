/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

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
                                .join(Query(ProjectInfos)).on(_.projectId === _.id)
                                .map{ case (a,p) => p -> a.level }.elements

    def getProjectUsers(project: Long)(implicit session: Session) =
      Query(ProjectAccessLevels).filter(_.projectId === project).elements
  }

  object SessionInfos extends Table[SessionInfo]("sessions") {
    def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def userName     = column[String]("name")
    def color        = column[String]("color")
    def projectId    = column[Long]("project")    
    def active       = column[Boolean]("active")
    def isHuman      = column[Boolean]("isHuman")
    def user         = foreignKey("fk_session_user", userName, UserInfos)(_.name,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)
    def project      = foreignKey("fk_session_project", projectId, ProjectInfos)(_.id,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)

    def * = id ~ userName ~ color ~ projectId ~ isHuman ~ active <> (SessionInfo.apply _, SessionInfo.unapply _)

    def create(user: String, color: String, project: Long, isHuman: Boolean, active: Boolean)(implicit session: Session) = {
      val q = this.id.? ~ this.userName ~ this.color ~ this.projectId ~ this.isHuman ~ this.active returning this.id
      val id = q.insert((None,user,color,project,isHuman,active))
      SessionInfo(id,user,color,project,isHuman,active)
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
     
    // TODO: Make single query
    def cleanProject(id: Long)(implicit session: Session) = {
      // delete duplicates and keep newest
      val newest = for {
        (name,ss) <- SessionInfos.filter(_.projectId === id) groupBy (_.userName) 
      } yield name -> ss.map(_.id).max
      
      val toDelete = for {        
        (name,newest) <- newest.elements        
      } {
        SessionInfos.filter(other => other.projectId === id && other.userName === name && other.id =!= newest).delete
      }
      // set all sessions to inactive
      Query(SessionInfos).map(_.active).update(false)
    }

    def getForProject(id: Long)(implicit session: Session) = 
      Query(SessionInfos).filter(_.projectId === id).elements

    def getForUser(name: String)(implicit session: Session) = 
      Query(SessionInfos).filter(_.userName === name).elements
  }
}
