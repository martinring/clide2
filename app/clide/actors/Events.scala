package clide.actors

import clide.models._

object Events {
  trait Event
  
  trait FileEvent extends Event
  case class FileCreated(file: FileInfo) extends FileEvent
  case class FileDeleted(file: FileInfo) extends FileEvent
  case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent
  
  trait UserEvent extends Event    
  case class SignedUp(user: UserInfo) extends UserEvent
  case class LoggedIn(user: UserInfo, login: LoginInfo) extends UserEvent
  case class LoggedOut(user: UserInfo) extends UserEvent
  case class DoesntExist(name: String) extends UserEvent
  case class WrongPassword(user: UserInfo) extends UserEvent
  case class SessionTimedOut(user: UserInfo) extends UserEvent
  case object NotLoggedIn extends UserEvent
  case class NotAllowed(user: UserInfo) extends UserEvent
  case class Validated(user: UserInfo, login: LoginInfo) extends UserEvent
  
  trait ProjectEvent extends Event
  case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent
}