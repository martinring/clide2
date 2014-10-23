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
import clide.collaboration.Operation

trait FileTables { this: Profile with ProjectTables with Mappers =>
  import profile.simple._
    
  implicit val pathMapper = MappedColumnType.base[Seq[String], String](
    _.mkString("/") , _.split('/').toSeq.filter(!_.isEmpty()))
    
  class FileInfos(tag: Tag) extends Table[FileInfo](tag, "files") {
    def id          = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def projectId   = column[Long]("projectId")
    def path        = column[Seq[String]]("path")
    def mimeType    = column[Option[String]]("mimeType")
    def deleted     = column[Boolean]("deleted")
    def exists      = column[Boolean]("exists")
    def isDirectory = column[Boolean]("isDirectory")
    def parentId    = column[Option[Long]]("parent")

    def project     = foreignKey("fk_fileInfos_project", projectId, projectInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)

    def parent      = foreignKey("fk_fileInfos_parent", parentId, fileInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)

    def projectPath = index("project_path", (projectId,path), unique = true)

    def * = (id, projectId, path, mimeType, deleted, exists, isDirectory, parentId) <> (FileInfo.tupled, FileInfo.unapply)
  }
  
  val fileInfos = TableQuery[FileInfos]
  
  object FileInfos {
    def create(fileInfo: FileInfo)(implicit session: Session) = {
      val id = fileInfos.returning(fileInfos.map(_.id)).insert(fileInfo)
      fileInfo.copy(id = id)
    }

    def get(project: ProjectInfo, path: Seq[String])(implicit session: Session): Option[FileInfo] = 
      fileInfos.filter(f => f.projectId === project.id && f.path === path).firstOption

    def get(id: Long)(implicit session: Session) =
      fileInfos.filter(_.id === id).firstOption

    def getChildren(id: Long)(implicit session: Session): List[FileInfo] =
      fileInfos.filter(_.parentId === id).list

    def update(file: FileInfo)(implicit session: Session) =
      fileInfos.filter(_.id === file.id).update(file)

    def delete(file: FileInfo)(implicit session: Session) =
      fileInfos.filter(_.id === file.id).delete
  }

  class OpenedFiles(tag: Tag) extends Table[(Long,Long)](tag, "openFiles") {
    implicit val pathMapper = MappedColumnType.base[Seq[String], String](
        _.mkString("/") , _.split('/').toSeq.filter(!_.isEmpty()))

    def sessionId   = column[Long]("session")
    def fileId      = column[Long]("file")

    def session = foreignKey("fk_openFile_session", sessionId, sessionInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)
    def file = foreignKey("fk_openFile_file", fileId, fileInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)
    def pk = primaryKey("pk_openFile", (sessionId,fileId))

    def * = (sessionId, fileId)
  }
  
  val openedFiles = TableQuery[OpenedFiles]
  
  object OpenedFiles {
    def get(sessionId: Long)(implicit session: Session) = {
      val q = for {
        openFile <- openedFiles if openFile.sessionId === sessionId
        file <- openFile.file
      } yield file
      q.list
    }

    def create(session: Long, file: Long)(implicit s: Session) = {
      openedFiles.insert((session,file))
    }

    def delete(session: Long, file: Long)(implicit s: Session) = {
      val q = for (f <- openedFiles if f.sessionId === session && f.fileId === file) yield f
      q.delete
    }
  }

  class Revisions(tag: Tag) extends Table[Revision](tag, "revisions") {
    def fileId  = column[Long]("fileId")
    def id      = column[Long]("id")

    def content = column[Operation[Char]]("content")

    def file = foreignKey("fk_revision_file", fileId, fileInfos)(_.id,
        ForeignKeyAction.Cascade,
        ForeignKeyAction.Cascade)

    def fileRevision = index("file_revision", (fileId,id), unique = true)

    def * = (fileId, id, content) <> (Revision.tupled,Revision.unapply)
  }
  
  val revisions = TableQuery[Revisions]
  
  object Revisions {
    def get(file: Long)(implicit session: Session) =
      revisions.filter(_.fileId === file)
                      .sortBy(_.id.asc)
                      .map(_.content)
                      .list

    def clear(file: Long)(implicit session: Session) =
      revisions.filter(_.fileId === file)
                      .delete

    def create(file: Long, id: Long, content: Operation[Char])(implicit session: Session) =
      revisions.insert(Revision(file,id,content))
  }
}
