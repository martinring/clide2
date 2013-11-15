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
import clide.collaboration.Operation
import clide.collaboration.Annotations

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Messages {
  trait Message

  case object Register extends Message
  case object Unregister extends Message

  case object ForgetIt extends Message

  trait UserServerMessage extends Message
  case class SignUp(name: String, email: String, password: String) extends UserServerMessage
  case class IdentifiedFor(user: String, key: String, message: UserMessage) extends UserServerMessage
  case class AnonymousFor(user: String, message: UserMessage) extends UserServerMessage

  trait UserMessage extends Message
  case object Validate extends UserMessage
  case class Login(password: String) extends UserMessage
  case object Logout extends UserMessage
  case class CreateProject(name: String, description: Option[String]) extends UserMessage
  case class WithUser(name: String, message: UserMessage) extends UserMessage with SessionMessage
  case class WithProject(name: String, message: ProjectMessage) extends UserMessage
  case object BrowseProjects extends UserMessage
  case class Invite(project: String) extends UserMessage
  case class StartSession(project: String) extends UserMessage
  case object StartBackstageSession extends UserMessage
  case object RequestBackstageInfo extends UserMessage with SessionMessage

  trait ProjectMessage extends Message
  case object DeleteProject extends ProjectMessage

  case class WithPath(path: Seq[String], message: FileMessage) extends ProjectMessage with FileMessage
  case object StartFileBrowser      extends ProjectMessage
  case object StartSession          extends ProjectMessage

  case class ChangeProjectUserLevel(user: String, level: ProjectAccessLevel.Value) extends ProjectMessage

  trait FileMessage        extends Message
  trait FileReadMessage    extends FileMessage
  trait FileWriteMessage   extends FileReadMessage

  case object BrowseFolder extends FileReadMessage
  case object ExplorePath  extends FileReadMessage
  case object TouchFile    extends FileWriteMessage
  case object TouchFolder  extends FileWriteMessage
  case object NewFile      extends FileWriteMessage
  case object Delete       extends FileWriteMessage
  case object SaveFile     extends FileWriteMessage

  case object EOF extends Message

  trait SessionMessage extends Message
  case object EnterSession extends SessionMessage
  case object LeaveSession extends SessionMessage
  case object CloseSession extends SessionMessage
  case object RequestSessionInfo extends SessionMessage
  case class Talk(to: Option[Long], msg: String, tpe: Option[String]) extends SessionMessage with ProjectMessage
  case class SetColor(value: String) extends SessionMessage
  case class SwitchFile(id: Long) extends SessionMessage
  case class OpenFile(id: Long) extends SessionMessage
  case class CloseFile(id: Long) extends SessionMessage
  case class Edit(id: Long, revision: Long, operation: Operation) extends SessionMessage with FileWriteMessage
  case class Annotate(id: Long, revision: Long, annotation: Annotations, name: String) extends SessionMessage with FileReadMessage

  private[actors] object internal {
    trait UserMessageWrapper
	case class Identified(key: String, message: UserMessage) extends UserMessageWrapper
	case class Anonymous(message: UserMessage) extends UserMessageWrapper
	case class External(sender: UserInfo, message: UserMessage) extends UserMessageWrapper

    case class WrappedProjectMessage(
      user: UserInfo,
      level: ProjectAccessLevel.Value,
      message: ProjectMessage)

    case class OpenFile(user: SessionInfo) extends FileReadMessage
  }
}
