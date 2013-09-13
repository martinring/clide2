package clide.actors

import clide.models._
import play.api.libs.json.Json

object Messages {
  trait Message	

  case object Register extends Message
  case object Unregister extends Message

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
    
  case class WrappedProjectMessage(
      level: ProjectAccessLevel.Value, 
      message: ProjectMessage)
  
  trait ProjectMessage extends Message
  object DeleteProject extends ProjectMessage

  case class WithPath(path: Seq[String], message: FileMessage) extends ProjectMessage

  trait FileMessage        extends Message
  trait FileReadMessage    extends FileMessage
  trait FileWriteMessage   extends FileMessage
  case object OpenFile     extends FileReadMessage
  case object BrowseFolder extends FileReadMessage
  case object Delete       extends FileWriteMessage
  case object SaveFile     extends FileWriteMessage
  
  // JSON 
  implicit val readCreateProject = Json.reads[CreateProject]
}