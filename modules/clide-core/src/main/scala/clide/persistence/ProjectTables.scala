/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
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

trait ProjectTables { this: Profile with Mappers with UserTables with FileTables =>
  import profile.simple._

  class ProjectInfos(tag: Tag) extends Table[ProjectInfo](tag,"projects") {
    def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def name         = column[String]("name")
    def ownerName    = column[String]("owner")
    def description  = column[Option[String]]("description")
    def public       = column[Boolean]("public")
    def owner        = foreignKey("fk_project_user", ownerName, userInfos)(_.name,
        ForeignKeyAction.Cascade, // update
        ForeignKeyAction.Cascade) // delete
    def *            = (id, name, ownerName, description, public) <> (ProjectInfo.tupled, ProjectInfo.unapply)
    // for every owner, the names of all his projects must be unique
    // which means, that project names alone don't have to be.    
    def ownerProject = index("idx_owner_project", (ownerName, name), unique = true)
  }

  val projectInfos = TableQuery[ProjectInfos]
  
  object ProjectInfos {
    def create(project: ProjectInfo)(implicit session: Session) = {
      val id = projectInfos.returning(projectInfos.map(_.id)) += project      
      project.copy(id = id)      
    }

    def delete(id: Long)(implicit session: Session) =
      projectInfos.filter(_.id === id).delete

    def delete(p: ProjectInfo)(implicit session: Session) =
      projectInfos.filter(_.id === p.id).delete

    def update(p: ProjectInfo)(implicit session: Session) =
      projectInfos.filter(_.id === p.id).update(p)

    def getByOwner(owner: String)(implicit session: Session) =
      projectInfos.filter(_.ownerName === owner).list

    def get(owner: String, name: String)(implicit session: Session) =
      projectInfos.filter(_.ownerName === owner)
                  .filter(_.name === name).list

    def get(id: Long)(implicit session: Session) =
      projectInfos.filter(_.id === id).firstOption

    def getPublic(implicit session: Session) =
      projectInfos.filter(_.public === true).list
  }

  class ProjectAccessLevels(tag: Tag) extends Table[(Long,String,ProjectAccessLevel.Value)](tag,"rights") {
    def projectId = column[Long]("project")
    def userName  = column[String]("user")
    def project   = foreignKey("fk_right_project", projectId, projectInfos)(_.id,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)
    def user      = foreignKey("fk_right_user", userName, userInfos)(_.name,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)
    def pk        = primaryKey("pk_right", (projectId,userName))
    def level     = column[ProjectAccessLevel.Value]("policy")
    def *         = (projectId, userName, level)
  }
  
  val projectAccessLevels = TableQuery[ProjectAccessLevels]

  object ProjectAccessLevels {
    def change(project: Long, user: String, level: ProjectAccessLevel.Value)(implicit session: Session) = {
      level match {
        case ProjectAccessLevel.None =>
          projectAccessLevels.filter(l => l.projectId === project && l.userName === user).delete
        case level => // TODO: Transaction?
          val q = projectAccessLevels.filter(l => l.projectId === project && l.userName === user)
          q.firstOption match {
            case None          => projectAccessLevels += (project,user,level)
            case Some((p,u,l)) => q.update((p,u,level))
          }
      }
    }

    def getUserProjects(user: String)(implicit session: Session) =
      projectAccessLevels.filter(_.userName === user)
                         .join(projectInfos).on(_.projectId === _.id)
                         .map{ case (a,p) => p -> a.level }.list

    def getProjectUsers(project: Long)(implicit session: Session) =
      projectAccessLevels.filter(_.projectId === project).list
  }

  class SessionInfos(tag: Tag) extends Table[SessionInfo](tag, "sessions") {
    def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def userName     = column[String]("name")
    def color        = column[String]("color")
    def projectId    = column[Long]("project")
    def active       = column[Boolean]("active")
    def isHuman      = column[Boolean]("isHuman")
    def user         = foreignKey("fk_session_user", userName, userInfos)(_.name,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)
    def project      = foreignKey("fk_session_project", projectId, projectInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)

    def * = (id, userName, color, projectId, isHuman, active) <> (SessionInfo.tupled, SessionInfo.unapply)
  }
  
  val sessionInfos = TableQuery[SessionInfos]
  
  object SessionInfos {
    def create(sessionInfo: SessionInfo)(implicit session: Session) = {      
      val id = sessionInfos.returning(sessionInfos.map(_.id)) += sessionInfo
      sessionInfo.copy(id = id)
    }

    def update(info: SessionInfo)(implicit session: Session) = {
      val q = for (i <- sessionInfos if i.id === info.id) yield i
      q.update(info)
    }

    def delete(info: SessionInfo)(implicit session: Session) = {
      val q = for (i <- sessionInfos if i.id === info.id) yield i
      q.delete
    }

    def get(id: Long)(implicit session: Session) = {
      val q = for (i <- sessionInfos if i.id === id) yield i
      q.firstOption
    }

    // TODO: Make single query
    def cleanProject(id: Long)(implicit session: Session) = {
      // delete duplicates and keep newest
      val newest = for {
        (name,ss) <- sessionInfos.filter(_.projectId === id) groupBy (_.userName)
      } yield name -> ss.map(_.id).max

      val toDelete = for {
        (name,newest) <- newest.list
      } {
        sessionInfos.filter(other => other.projectId === id && other.userName === name && other.id =!= newest).delete
      }
      // set all sessions to inactive
      sessionInfos.map(_.active).update(false)
    }

    def getForProject(id: Long)(implicit session: Session) =
      sessionInfos.filter(_.projectId === id).list

    def getForUser(name: String)(implicit session: Session) =
      sessionInfos.filter(_.userName === name).list
  }
}
