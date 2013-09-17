package clide.actors

import clide.models._
import play.api.libs.json.Json
import clide.collaboration.Operation
import clide.collaboration.AnnotationStream

object Messages {
  trait Message	

  case object Register extends Message
  case object Unregister extends Message

  case object ForgetIt extends Message
  
  trait UserServerMessage extends Message
  case class SignUp(name: String, email: String, password: String) extends UserServerMessage
  case class IdentifiedFor(user: String, key: String, message: UserMessage) extends UserServerMessage
  case class AnonymousFor(user: String, message: UserMessage) extends UserServerMessage
  // TODO: Support anonymous requests
  
  trait UserMessageWrapper
  case class Identified(key: String, message: UserMessage) extends UserMessageWrapper
  case class Anonymous(message: UserMessage) extends UserMessageWrapper
  // TODO: Should be private
  case class External(sender: UserInfo, message: UserMessage) extends UserMessageWrapper
  
  trait UserMessage  
  case object Validate extends UserMessage
  case class Login(password: String) extends UserMessage
  case object Logout extends UserMessage  
  case class CreateProject(name: String, description: Option[String]) extends UserMessage   
  case class WithUser(name: String, message: UserMessage) extends UserMessage  
  case class WithProject(name: String, message: ProjectMessage) extends UserMessage
  case object BrowseProjects extends UserMessage
  case class StartSession(project: String) extends UserMessage
    
  case class WrappedProjectMessage(
      user: UserInfo,
      level: ProjectAccessLevel.Value, 
      message: ProjectMessage)
  
  trait ProjectMessage extends Message
  object DeleteProject extends ProjectMessage 
  
  case class WithPath(path: Seq[String], message: FileMessage) extends ProjectMessage with FileMessage
  case object StartFileBrowser extends ProjectMessage
  case object StartSession     extends ProjectMessage

  trait FileMessage        extends Message
  trait FileReadMessage    extends FileMessage
  trait FileWriteMessage   extends FileMessage
  case object OpenFile     extends FileReadMessage
  case object BrowseFolder extends FileReadMessage
  case object ExplorePath  extends FileReadMessage
  case object TouchFile    extends FileWriteMessage
  case object NewFile      extends FileWriteMessage
  case object Delete       extends FileWriteMessage
  case object SaveFile     extends FileWriteMessage
  
  case object EOF extends Message
  
  trait SessionMessage extends Message  
  case object EnterSession extends SessionMessage
  case object LeaveSession extends SessionMessage
  case object CloseSession extends SessionMessage
  case object RequestSessionInfo extends SessionMessage
  case class SwitchFile(id: Long) extends SessionMessage
  case class Edit(revision: Long, operation: Operation) extends SessionMessage
  case class Annotate(revision: Long, annotation: AnnotationStream) extends SessionMessage    
  
  // JSON 
  implicit val readCreateProject = Json.reads[CreateProject]  
}