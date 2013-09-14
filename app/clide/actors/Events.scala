package clide.actors

import clide.models._
import play.api.libs.iteratee.Enumeratee
import play.api.mvc._
import play.api.libs.json._
import akka.actor.ActorRef
import play.api.libs.iteratee._
import clide.actors.Messages.Message
import scala.actors.Channel

object Events {
  trait Event  
  case object TimeOut extends Event
  case object UnexpectedTermination extends Event
    
  case class EventSocket(in: ActorRef) extends Event
  
  trait FileEvent extends Event
  case class FileCreated(file: FileInfo) extends FileEvent
  case class FileDeleted(file: FileInfo) extends FileEvent
  case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent
  
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
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent
      
  trait SessionEvent extends Event
  case object SessionStarted
  
  case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event          
      
  import Results._
  implicit def defaultResult(event: Event): SimpleResult = event match {
    case CreatedProject(info) => Ok(Json.toJson(info))
    case DeletedProject(info) => Ok    
    case DoesntExist => NotFound
    case SessionTimedOut => Unauthorized("timeout")
    case NotLoggedIn => Unauthorized
    case NotAllowed  => Forbidden
    case Validated(info) => Ok(Json.obj(
        "username" -> info.name, 
        "email" -> info.email))
    case UserProjectInfos(u,c) => Ok(Json.obj(
        "userProjects" -> Json.toJson(u),
        "collaborating" -> Json.toJson(u)))      
  } 
}