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
import slick.lifted.ForeignKeyAction
import clide.collaboration.Operation

trait FileTables { this: Profile with ProjectTables with Mappers =>
  import profile.simple._
  object FileInfos extends Table[FileInfo]("files") {
    implicit val pathMapper = MappedTypeMapper.base[Seq[String], String](
        _.mkString("/") , _.split('/').toSeq.filter(!_.isEmpty()))

    def id          = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def projectId   = column[Long]("projectId")
    def path        = column[Seq[String]]("path")
    def mimeType    = column[Option[String]]("mimeType")
    def deleted     = column[Boolean]("deleted")
    def exists      = column[Boolean]("exists")
    def isDirectory = column[Boolean]("isDirectory")
    def parentId    = column[Option[Long]]("parent")

    def project     = foreignKey("fk_fileInfos_project", projectId, ProjectInfos)(_.id,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)

    def parent      = foreignKey("fk_fileInfos_parent", parentId, FileInfos)(_.id,
        onUpdate = ForeignKeyAction.Cascade,
        onDelete = ForeignKeyAction.Cascade)

    def projectPath = index("project_path", (projectId,path), unique = true)

    def * = id ~ projectId ~ path ~ mimeType ~ deleted ~ exists ~ isDirectory ~ parentId <> (FileInfo.apply _, FileInfo.unapply _)

    def create(project: Long, path: Seq[String], mimeType: Option[String], deleted: Boolean, exists: Boolean, isDirectory: Boolean, parent: Option[Long])(implicit session: Session) = {
      val autoinc = this.id.? ~ this.projectId ~ this.path ~ this.mimeType ~ this.deleted ~ this.exists ~ this.isDirectory ~ this.parentId returning this.id
      val id = autoinc.insert((None,project,path,mimeType,deleted,exists,isDirectory,parent))
      FileInfo(id,project,path,mimeType,deleted,exists,isDirectory,parent)
    }

    def get(project: ProjectInfo, path: Seq[String]) = for {
      file <- FileInfos if file.projectId === project.id && file.path === path
    } yield file

    def get(id: Long) = for {
      file <- FileInfos if file.id === id
    } yield file

    def getChildren(id: Long) = for {
      file <- FileInfos if file.parentId === id
    } yield file
  }

  object OpenedFiles extends Table[(Long,Long)]("openFiles") {
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

    def get(sessionId: Long)(implicit session: Session) = {
      val q = for {
        openFile <- OpenedFiles if openFile.sessionId === sessionId
        file <- openFile.file
      } yield file
      q.elements
    }

    def create(session: Long, file: Long)(implicit s: Session) = {
      OpenedFiles.insert((session,file))
    }

    def delete(session: Long, file: Long)(implicit s: Session) = {
      val q = for (f <- OpenedFiles if f.sessionId === session && f.fileId === file) yield f
      q.delete
    }
  }

  object Revisions extends Table[Revision]("revisions") {
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
}
