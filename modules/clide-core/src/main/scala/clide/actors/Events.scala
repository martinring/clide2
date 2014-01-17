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
import clide.actors.Messages.BroadcastMessage

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Events {
  trait Event
  @SerialVersionUID(100000) case object TimeOut extends Event
  @SerialVersionUID(101000) case object UnexpectedTermination extends Event

  @SerialVersionUID(102000) case class ActionFailed(e: Map[String,String]) extends Event

  @SerialVersionUID(103000) case class FileInitFailed(file: Long) extends Event
  
  @SerialVersionUID(104000) case class EventSocket(in: ActorRef, id: String) extends Event
  @SerialVersionUID(105000) case object Welcome extends Event

  trait FileEvent extends Event
  @SerialVersionUID(106000) case class FileCreated(file: FileInfo) extends FileEvent
  @SerialVersionUID(107000) case class FileDeleted(file: FileInfo) extends FileEvent
  @SerialVersionUID(108000) case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent

  trait FileBrowserEvent extends FileEvent
  @SerialVersionUID(109000) case class FolderContent(folder: FileInfo, files: Seq[FileInfo]) extends FileBrowserEvent
  @SerialVersionUID(110000) case class FileId(id: FileInfo) extends FileBrowserEvent

  trait UserEvent extends Event
  @SerialVersionUID(111000) case class SignedUp(user: UserInfo) extends UserEvent
  @SerialVersionUID(112000) case class LoggedIn(user: UserInfo, login: LoginInfo) extends UserEvent
  @SerialVersionUID(113000) case class LoggedOut(user: UserInfo) extends UserEvent
 
  trait AuthEvent extends Event
  @SerialVersionUID(114000) case object DoesntExist extends AuthEvent
  @SerialVersionUID(115000) case object WrongPassword extends AuthEvent
  @SerialVersionUID(116000) case object SessionTimedOut extends AuthEvent
  @SerialVersionUID(117000) case object NotLoggedIn extends AuthEvent
  @SerialVersionUID(118000) case object NotAllowed extends AuthEvent
  @SerialVersionUID(119000) case class Validated(user: UserInfo) extends AuthEvent

  trait ProjectEvent extends Event
  @SerialVersionUID(120000) case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  @SerialVersionUID(121000) case class ProjectCouldNotBeCreated(reason: String) extends ProjectEvent
  @SerialVersionUID(122000) case class DeletedProject(project: ProjectInfo) extends ProjectEvent
  @SerialVersionUID(123000) case class ChangedProjectUserLevel(project: ProjectInfo, user: String, level: ProjectAccessLevel.Value) extends ProjectEvent

  trait SessionEvent extends Event  
  @SerialVersionUID(124000) case class SessionInit(
      info: SessionInfo,
      collaborators: Set[SessionInfo],
      eventHistory: List[BroadcastEvent]) extends SessionEvent
  @SerialVersionUID(125000) case class SessionChanged(info: SessionInfo) extends SessionEvent
  @SerialVersionUID(126000) case class SessionStopped(info: SessionInfo) extends SessionEvent
  @SerialVersionUID(127000) case class FileClosed(id: Long) extends SessionEvent
  @SerialVersionUID(128000) case class FileOpened(file: OpenedFile) extends SessionEvent
  @SerialVersionUID(129000) case class Edited(file: Long, op: Operation) extends SessionEvent
  @SerialVersionUID(137000) case class AnnotationsOffered(file: Long, user: Long, name: String, description: Option[String]) extends SessionEvent
  @SerialVersionUID(138000) case class AnnotationsRequested(file: Long, name: String) extends SessionEvent
  @SerialVersionUID(139000) case class AnnotationsDisregarded(file: Long, name: String) extends SessionEvent
  @SerialVersionUID(130000) case class Annotated(file: Long, user: Long, an: Annotations, name: String) extends SessionEvent
  @SerialVersionUID(131000) case class AnnotationsClosed(file: Long, user: Long, name: String) extends SessionEvent
  // TODO case class AnnotationChanged(file: Long, user: Long, an: AnnotationDiff, name: String) extends SessionEvent
  @SerialVersionUID(132000) case class AcknowledgeEdit(file: Long) extends SessionEvent
  @SerialVersionUID(133000) case class MetaInfo(file: Long, info: Map[String,String]) extends SessionEvent
  @SerialVersionUID(134000) case object Kicked extends SessionEvent
    
  /**
   * @param who the session id of the collaborator processing the file
   */
  @SerialVersionUID(135000) case class BroadcastEvent(who: Long, timestamp: Long, msg: BroadcastMessage) extends SessionEvent  
  
  /**
   * Used to transmit all the projects of a user
   * @param userProject   the projects owned by the user
   * @param collaborating the projects the user collaborates in
   */
  @SerialVersionUID(136000) case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event

  private[actors] object internal {
    case class OTState(info: FileInfo, content: String, revision: Long) extends SessionEvent
  }
}
