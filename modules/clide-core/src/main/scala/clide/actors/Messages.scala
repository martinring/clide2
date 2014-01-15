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
package clide.actors

import clide.models._
import clide.collaboration.Operation
import clide.collaboration.Annotations

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Messages {
  trait Message

  @SerialVersionUID(10000) case object Register extends Message
  @SerialVersionUID(20000) case object Unregister extends Message
  @SerialVersionUID(30000) case object ForgetIt extends Message

  trait UserServerMessage extends Message
  // FIXME: Security: plain password!!!
  @SerialVersionUID(40000) case class SignUp(name: String, email: String, password: String) extends UserServerMessage
  @SerialVersionUID(50000) case class IdentifiedFor(user: String, key: String, message: UserMessage) extends UserServerMessage
  @SerialVersionUID(60000) case class AnonymousFor(user: String, message: UserMessage) extends UserServerMessage

  trait UserMessage extends Message
  @SerialVersionUID(70000) case object Validate extends UserMessage
  @SerialVersionUID(80000) case class Login(password: String, isHuman: Boolean = false) extends UserMessage
  @SerialVersionUID(90000) case object Logout extends UserMessage
  @SerialVersionUID(100000) case class CreateProject(name: String, description: Option[String], public: Boolean) extends UserMessage
  @SerialVersionUID(110000) case class WithUser(name: String, message: UserMessage) extends UserMessage with SessionMessage
  @SerialVersionUID(120000) case class WithProject(name: String, message: ProjectMessage) extends UserMessage
  @SerialVersionUID(130000) case object BrowseProjects extends UserMessage
  @SerialVersionUID(140000) case class Invite(project: String) extends UserMessage
  @SerialVersionUID(150000) case class StartSession(project: String) extends UserMessage
  @SerialVersionUID(160000) case object StartBackstageSession extends UserMessage
  @SerialVersionUID(170000) case object RequestBackstageInfo extends UserMessage with SessionMessage

  trait ProjectMessage extends Message
  @SerialVersionUID(180000) case object DeleteProject extends ProjectMessage

  @SerialVersionUID(190000) case class WithPath(path: Seq[String], message: FileMessage) extends ProjectMessage with FileMessage
  @SerialVersionUID(200000) case object StartFileBrowser      extends ProjectMessage
  @SerialVersionUID(210000) case object StartSession          extends ProjectMessage

  @SerialVersionUID(220000) case class ChangeProjectUserLevel(user: String, level: ProjectAccessLevel.Value) extends ProjectMessage

  trait FileMessage        extends Message
  trait FileReadMessage    extends FileMessage
  trait FileWriteMessage   extends FileReadMessage

  @SerialVersionUID(230000) case object BrowseFolder extends FileReadMessage
  @SerialVersionUID(240000) case object ExplorePath  extends FileReadMessage
  @SerialVersionUID(250000) case object TouchFile    extends FileWriteMessage
  @SerialVersionUID(260000) case object TouchFolder  extends FileWriteMessage
  @SerialVersionUID(270000) case object NewFile      extends FileWriteMessage
  @SerialVersionUID(280000) case object Delete       extends FileWriteMessage
  @SerialVersionUID(290000) case object SaveFile     extends FileWriteMessage

  @SerialVersionUID(300000) case object EOF extends Message

  trait SessionMessage extends Message
  @SerialVersionUID(310000) case object EnterSession extends SessionMessage
  @SerialVersionUID(320000) case object LeaveSession extends SessionMessage
  @SerialVersionUID(330000) case object CloseSession extends SessionMessage
  @SerialVersionUID(340000) case object RequestSessionInfo extends SessionMessage  
  @SerialVersionUID(350000) case class SetColor(value: String) extends SessionMessage
  @SerialVersionUID(360000) case class OpenFile(id: Long) extends SessionMessage
  @SerialVersionUID(370000) case class CloseFile(id: Long) extends SessionMessage
  @SerialVersionUID(380000) case class Kick(id: Long) extends SessionMessage with ProjectMessage
  @SerialVersionUID(390000) case class Edit(id: Long, revision: Long, operation: Operation) extends SessionMessage with FileWriteMessage
  @SerialVersionUID(400000) case class Annotate(id: Long, revision: Long, annotation: Annotations, name: String) extends SessionMessage with FileReadMessage
  @SerialVersionUID(700000) case class SubscribeToAnnotations(id: Long, user: String, name: String) extends SessionMessage
  @SerialVersionUID(710000) case class UnsubscribeFromAnnotations(id: Long, user: String, name: String) extends SessionMessage
  
  trait BroadcastMessage extends SessionMessage
  
  @SerialVersionUID(410000) case class Talk(to: Option[Long], msg: String, tpe: Option[String]) extends BroadcastMessage
  
  trait ProcessingMessage extends BroadcastMessage
  @SerialVersionUID(420000) case class LookingAtFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(430000) case class StoppedLookingAtFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(440000) case class WorkingOnFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(450000) case class ProgressOnFile(file: Long, progress: Double) extends ProcessingMessage
  @SerialVersionUID(460000) case class DoneWithFile(file: Long) extends ProcessingMessage
  @SerialVersionUID(470000) case class FailureInFile(file: Long, msg: Option[String]) extends ProcessingMessage

  private[actors] object internal {
    trait UserMessageWrapper extends Message
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
