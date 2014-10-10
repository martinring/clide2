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
package clide.actors

import clide.models._
import clide.collaboration.Operation
import clide.collaboration.Annotations

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Messages {
  sealed trait Message

  @SerialVersionUID(1L) case object Register extends Message
  @SerialVersionUID(1L) case object Unregister extends Message
  @SerialVersionUID(1L) case object ForgetIt extends Message

  sealed trait UserServerMessage extends Message
  // FIXME: Security: plain password!!!
  @SerialVersionUID(1L) case class SignUp(name: String, email: String, password: String) extends UserServerMessage
  @SerialVersionUID(1L) case class IdentifiedFor(user: String, key: String, message: UserMessage) extends UserServerMessage
  @SerialVersionUID(1L) case class AnonymousFor(user: String, message: UserMessage) extends UserServerMessage

  sealed trait UserMessage extends Message
  @SerialVersionUID(1L) case object Validate extends UserMessage
  @SerialVersionUID(1L) case class Login(password: String, isHuman: Boolean = false) extends UserMessage
  @SerialVersionUID(1L) case object Logout extends UserMessage
  @SerialVersionUID(1L) case class CreateProject(name: String, description: Option[String], public: Boolean) extends UserMessage
  @SerialVersionUID(1L) case class WithUser(name: String, message: UserMessage) extends UserMessage with SessionMessage
  @SerialVersionUID(1L) case class WithProject(name: String, message: ProjectMessage) extends UserMessage
  @SerialVersionUID(1L) case object BrowseProjects extends UserMessage
  @SerialVersionUID(1L) case class Invite(project: String) extends UserMessage
  @SerialVersionUID(1L) case class StartSession(project: String) extends UserMessage
  @SerialVersionUID(1L) case object StartBackstageSession extends UserMessage
  @SerialVersionUID(1L) case object RequestBackstageInfo extends UserMessage with SessionMessage

  sealed trait ProjectMessage extends Message
  @SerialVersionUID(1L) case object DeleteProject extends ProjectMessage

  @SerialVersionUID(1L) case class WithPath(path: Seq[String], message: FileMessage) extends ProjectMessage with FileMessage
  @SerialVersionUID(1L) case object StartFileBrowser      extends ProjectMessage
  @SerialVersionUID(1L) case object StartSession          extends ProjectMessage

  @SerialVersionUID(1L) case class ChangeProjectUserLevel(user: String, level: ProjectAccessLevel.Value) extends ProjectMessage

  sealed trait FileMessage        extends Message
  sealed trait FileReadMessage    extends FileMessage
  sealed trait FileWriteMessage   extends FileReadMessage

  @SerialVersionUID(1L) case object BrowseFolder extends FileReadMessage
  @SerialVersionUID(1L) case object ExplorePath  extends FileReadMessage
  @SerialVersionUID(1L) case object TouchFile    extends FileWriteMessage
  @SerialVersionUID(1L) case object TouchFolder  extends FileWriteMessage
  @SerialVersionUID(1L) case object NewFile      extends FileWriteMessage
  @SerialVersionUID(1L) case object Delete       extends FileWriteMessage
  @SerialVersionUID(1L) case object SaveFile     extends FileWriteMessage

  @SerialVersionUID(1L) case object EOF extends Message

  sealed trait SessionMessage extends Message
  @SerialVersionUID(1L) case object EnterSession extends SessionMessage
  @SerialVersionUID(1L) case object LeaveSession extends SessionMessage
  @SerialVersionUID(1L) case object CloseSession extends SessionMessage
  @SerialVersionUID(1L) case object RequestSessionInfo extends SessionMessage
  @SerialVersionUID(1L) case class SetColor(value: String) extends SessionMessage
  @SerialVersionUID(1L) case class OpenFile(id: Long) extends SessionMessage
  @SerialVersionUID(1L) case class CloseFile(id: Long) extends SessionMessage
  @SerialVersionUID(1L) case class Kick(id: Long) extends SessionMessage with ProjectMessage
  @SerialVersionUID(1L) case class Edit(id: Long, revision: Long, operation: Operation) extends SessionMessage with FileWriteMessage
  @SerialVersionUID(1L) case class Annotate(id: Long, revision: Long, annotation: Annotations, name: String) extends SessionMessage with FileReadMessage
  @SerialVersionUID(1L) case class SubscribeToAnnotations(id: Long, user: Long, name: String) extends SessionMessage with FileReadMessage
  @SerialVersionUID(1L) case class UnsubscribeFromAnnotations(id: Long, user: Long, name: String) extends SessionMessage with FileReadMessage
  @SerialVersionUID(1L) case class OfferAnnotations(id: Long, name: String, description: Option[String]) extends SessionMessage with FileReadMessage

  sealed trait BroadcastMessage extends SessionMessage

  @SerialVersionUID(1L) case class Talk(to: Option[Long], msg: String, tpe: Option[String]) extends BroadcastMessage

  sealed trait ProcessingMessage extends BroadcastMessage
  @SerialVersionUID(1L) case class LookingAtFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(1L) case class StoppedLookingAtFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(1L) case class WorkingOnFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(1L) case class ProgressOnFile(file: Long, progress: Double) extends ProcessingMessage
  @SerialVersionUID(1L) case class DoneWithFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(1L) case class FailureInFile(file: Long, msg: Option[String]) extends ProcessingMessage

  private[actors] object internal {
    sealed trait UserMessageWrapper extends Message
  	case class Identified(key: String, message: UserMessage) extends UserMessageWrapper
  	case class Anonymous(message: UserMessage) extends UserMessageWrapper
  	case class External(sender: UserInfo, login: LoginInfo, message: UserMessage) extends UserMessageWrapper

    case class WrappedProjectMessage(
      user: UserInfo,
      isHuman: Boolean,
      level: ProjectAccessLevel.Value,
      message: ProjectMessage)

    case class OpenFile(user: SessionInfo) extends FileReadMessage
  }
}
