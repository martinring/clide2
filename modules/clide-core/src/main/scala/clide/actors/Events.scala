 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
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
import clide.actors.Messages.BroadcastMessage

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Events {
  trait Event
  @SerialVersionUID(1L) case object TimeOut extends Event
  @SerialVersionUID(1L) case object UnexpectedTermination extends Event

  @SerialVersionUID(1L) case class ActionFailed(e: Map[String,String]) extends Event

  @SerialVersionUID(1L) case class FileInitFailed(file: Long) extends Event

  @SerialVersionUID(1L) case class EventSocket(in: ActorRef, id: String) extends Event
  @SerialVersionUID(1L) case object Welcome extends Event

  trait FileEvent extends Event
  @SerialVersionUID(1L) case class FileCreated(file: FileInfo) extends FileEvent
  @SerialVersionUID(1L) case class FileDeleted(file: FileInfo) extends FileEvent
  @SerialVersionUID(1L) case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent

  trait FileBrowserEvent extends FileEvent
  @SerialVersionUID(1L) case class FolderContent(folder: FileInfo, files: Seq[FileInfo]) extends FileBrowserEvent
  @SerialVersionUID(1L) case class FileId(id: FileInfo) extends FileBrowserEvent

  trait UserEvent extends Event
  @SerialVersionUID(1L) case class SignedUp(user: UserInfo) extends UserEvent
  @SerialVersionUID(1L) case class LoggedIn(user: UserInfo, login: LoginInfo) extends UserEvent
  @SerialVersionUID(1L) case class LoggedOut(user: UserInfo) extends UserEvent

  trait AuthEvent extends Event
  @SerialVersionUID(1L) case object DoesntExist extends AuthEvent
  @SerialVersionUID(1L) case object WrongPassword extends AuthEvent
  @SerialVersionUID(1L) case object SessionTimedOut extends AuthEvent
  @SerialVersionUID(1L) case object NotLoggedIn extends AuthEvent
  @SerialVersionUID(1L) case object NotAllowed extends AuthEvent
  @SerialVersionUID(1L) case class Validated(user: UserInfo) extends AuthEvent

  trait ProjectEvent extends Event
  @SerialVersionUID(1L) case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  @SerialVersionUID(1L) case class ProjectCouldNotBeCreated(reason: String) extends ProjectEvent
  @SerialVersionUID(1L) case class DeletedProject(project: ProjectInfo) extends ProjectEvent
  @SerialVersionUID(1L) case class ChangedProjectUserLevel(project: ProjectInfo, user: String, level: ProjectAccessLevel.Value) extends ProjectEvent

  trait SessionEvent extends Event
  @SerialVersionUID(1L) case class SessionInit(
      info: SessionInfo,
      collaborators: Set[SessionInfo],
      eventHistory: List[BroadcastEvent]) extends SessionEvent
  @SerialVersionUID(1L) case class SessionChanged(info: SessionInfo) extends SessionEvent
  @SerialVersionUID(1L) case class SessionStopped(info: SessionInfo) extends SessionEvent
  @SerialVersionUID(1L) case class FileClosed(id: Long) extends SessionEvent
  @SerialVersionUID(1L) case class FileOpened(file: OpenedFile) extends SessionEvent
  @SerialVersionUID(1L) case class Edited(file: Long, op: Operation) extends SessionEvent
  @SerialVersionUID(1L) case class AnnotationsOffered(file: Long, user: Long, name: String, description: Option[String]) extends SessionEvent
  @SerialVersionUID(1L) case class AnnotationsRequested(file: Long, name: String) extends SessionEvent
  @SerialVersionUID(1L) case class AnnotationsDisregarded(file: Long, name: String) extends SessionEvent
  @SerialVersionUID(1L) case class Annotated(file: Long, user: Long, an: Annotations, name: String) extends SessionEvent
  @SerialVersionUID(1L) case class AnnotationsClosed(file: Long, user: Long, name: String) extends SessionEvent
  // TODO case class AnnotationChanged(file: Long, user: Long, an: AnnotationDiff, name: String) extends SessionEvent
  @SerialVersionUID(1L) case class AcknowledgeEdit(file: Long) extends SessionEvent
  @SerialVersionUID(1L) case class MetaInfo(file: Long, info: Map[String,String]) extends SessionEvent
  @SerialVersionUID(1L) case object Kicked extends SessionEvent

  /**
   * @param who the session id of the collaborator processing the file
   */
  @SerialVersionUID(1L) case class BroadcastEvent(who: Long, timestamp: Long, msg: BroadcastMessage) extends SessionEvent

  /**
   * Used to transmit all the projects of a user
   * @param userProject   the projects owned by the user
   * @param collaborating the projects the user collaborates in
   */
  @SerialVersionUID(1L) case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event

  private[actors] object internal {
    case class OTState(info: FileInfo, content: String, revision: Long) extends SessionEvent
  }
}
