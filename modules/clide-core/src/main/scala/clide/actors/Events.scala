 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 **                                                                           **
 **  This file is part of Clide.                                              **
 **                                                                           **
 **  Clide is free software: you can redistribute it and/or modify            **
 **  it under the terms of the GNU General Public License as published by     **
 **  the Free Software Foundation, either version 3 of the License, or        **
 **  (at your option) any later version.                                      **
 **                                                                           **
 **  Clide is distributed in the hope that it will be useful,                 **
 **  but WITHOUT ANY WARRANTY; without even the implied warranty of           **
 **  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
 **  GNU General Public License for more details.                             **
 **                                                                           **
 **  You should have received a copy of the GNU General Public License        **
 **  along with Clide.  If not, see <http://www.gnu.org/licenses/>.           **
 \*                                                                           */
package clide.actors

import clide.models._
import akka.actor.ActorRef
import clide.collaboration.Operation
import clide.collaboration.Annotations
import clide.collaboration.AnnotationDiff.AnnotationDiff

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Events {
  trait Event
  case object TimeOut extends Event
  case object UnexpectedTermination extends Event

  case class ActionFailed(e: Map[String,String]) extends Event

  case class FileInitFailed(file: Long) extends Event

  case class EventSocket(in: ActorRef, id: String) extends Event
  case object Welcome extends Event

  trait FileEvent extends Event
  case class FileCreated(file: FileInfo) extends FileEvent
  case class FileDeleted(file: FileInfo) extends FileEvent
  case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent

  trait FileBrowserEvent extends FileEvent
  case class FolderContent(folder: FileInfo, files: Seq[FileInfo]) extends FileBrowserEvent
  case class FileId(id: FileInfo) extends FileBrowserEvent

  trait UserEvent extends Event
  case class SignedUp(user: UserInfo) extends UserEvent
  case class LoggedIn(user: UserInfo, login: LoginInfo) extends UserEvent
  case class LoggedOut(user: UserInfo) extends UserEvent

  trait AuthEvent extends Event
  case object DoesntExist extends AuthEvent
  case object WrongPassword extends AuthEvent
  case object SessionTimedOut extends AuthEvent
  case object NotLoggedIn extends AuthEvent
  case object NotAllowed extends AuthEvent
  case class Validated(user: UserInfo) extends AuthEvent

  trait ProjectEvent extends Event
  case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  case class ProjectCouldNotBeCreated(reason: String) extends ProjectEvent
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent
  case class ChangedProjectUserLevel(project: ProjectInfo, user: String, level: ProjectAccessLevel.Value) extends ProjectEvent

  trait SessionEvent extends Event
  case class SessionInit(
      info: SessionInfo,
      collaborators: Set[SessionInfo],
      conversation: List[Talked]) extends SessionEvent
  case class SessionChanged(info: SessionInfo) extends SessionEvent
  case class SessionStopped(info: SessionInfo) extends SessionEvent
  case class FileSwitched(id: Option[Long]) extends SessionEvent
  case class FileClosed(id: Long) extends SessionEvent
  case class FileOpened(file: OpenedFile) extends SessionEvent
  case class Edited(file: Long, op: Operation) extends SessionEvent
  case class Annotated(file: Long, user: Long, an: Annotations, name: String) extends SessionEvent
  // TODO case class AnnotationChanged(file: Long, user: Long, an: AnnotationDiff, name: String) extends SessionEvent
  case class AcknowledgeEdit(file: Long) extends SessionEvent
  case class Talked(from: String, msg: String, tpe: Option[String], timestamp: Long) extends SessionEvent
  case class MetaInfo(file: Long, info: Map[String,String])

  case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event

  private[actors] object internal {
    case class OTState(info: FileInfo, content: String, revision: Long) extends SessionEvent
  }
}
