package clide.actors

import clide.models._

object Messages {
  trait Message	
  
  case object Register extends Message
  case object Unregister extends Message
  
  trait ServerMessage  extends Message
	
  trait UserServerMessage extends ServerMessage
  case class SignUp(name: String, email: String, password: String) extends UserServerMessage
  case class WithUser(name: String, message: UserMessage) extends UserServerMessage
	
  trait ProjectServerMessage extends ServerMessage
  case class CreateProject(owner: UserInfo, name: String, description: Option[String]) extends ProjectServerMessage
  case class WithProject(id: Long, message: ProjectMessage) extends ProjectServerMessage
	
  trait ProjectMessage extends ServerMessage
  object DeleteProject extends ProjectMessage
    
  case class WithPath(path: Seq[String], message: FileMessage) extends FileMessage with ProjectMessage
  
  trait FileMessage        extends Message
  case object OpenFile     extends FileMessage
  case object BrowseFolder extends FileMessage
  case object Delete       extends FileMessage
  case object SaveFile     extends FileMessage
  
  trait UserMessage    extends Message
  case class Login(password: String) extends UserMessage
  case class Logout(key: String) extends UserMessage
  case class Validate(key: String) extends UserMessage
  case class StartSession(key: String) extends UserMessage
}