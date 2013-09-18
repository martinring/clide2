package clide.actors

import clide.models._
import play.api.libs.iteratee.Enumeratee
import play.api.mvc._
import play.api.libs.json._
import akka.actor.ActorRef
import play.api.libs.iteratee._
import clide.actors.Messages.Message

object Events {
  trait Event  
  case object TimeOut extends Event
  case object UnexpectedTermination extends Event
    
  case class EventSocket(in: ActorRef) extends Event
  case object Welcome extends Event
  
  trait FileEvent extends Event
  case class FileCreated(file: FileInfo) extends FileEvent
  case class FileDeleted(file: FileInfo) extends FileEvent
  case class FileMoved(file: FileInfo, from: Seq[String]) extends FileEvent
  
  trait FileBrowserEvent extends FileEvent
  case class FolderContent(folder: FileInfo, files: Seq[FileInfo]) extends FileBrowserEvent
  case class FileId(id: FileInfo) extends FileBrowserEvent
  
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
  case class SessionInit(
      info: SessionInfo, 
      collaborators: Set[SessionInfo],
      openFiles: Set[FileInfo],
      activeFile: Option[Long]) extends SessionEvent
  case class SessionChanged(info: SessionInfo) extends SessionEvent
  case class SessionStopped(info: SessionInfo) extends SessionEvent  
  
  case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event          
      
  import Results._
  implicit def defaultResult(event: Event): SimpleResult = event match {
    case CreatedProject(info) => Ok(Json.toJson(info))
    case DeletedProject(info) => Ok
    case DoesntExist => NotFound("The requested resource doesn't exist (anymore).")
    case SessionTimedOut => Unauthorized("timeout")
    case NotLoggedIn => Unauthorized("You are not logged in.")
    case NotAllowed  => Forbidden("You are not allowed to access this resource")
    case TimeOut => Results.InternalServerError("An error occurred while processing your request on the server. :(")
    case Validated(info) => Ok(Json.obj(
        "username" -> info.name, 
        "email" -> info.email))
    case UserProjectInfos(u,c) => Ok(Json.obj(
        "userProjects" -> Json.toJson(u),
        "collaborating" -> Json.toJson(u)))    
  }
  
  private def error(error: String) = Json.obj("t"->"e","c"->error)
  
  private implicit def jsontype(name: String) = new {
    def of[T](content: T)(implicit writes: Writes[T]) = Json.obj("t"->name,"c"->content)
  }
  
  private implicit def plain(name: String) = Json.obj("t"->name)
  
  def serialize(event: Event): JsValue = event match {
    case TimeOut => error("the request timed out")
    case Welcome => "welcome"
    case UnexpectedTermination => error("internal server error (unexpected termination)")
    case SignedUp(user) => "signedup" of user
    case LoggedIn(user,login) => "loggedin" of user
    case LoggedOut(user) => "loggedout"
    case FolderContent(folder,files) => Json.obj("t"->"folder","info"->folder,"files"->files)
    case CreatedProject(p) => "createdproject" of p
    case DeletedProject(p) => "deletedproject" of p.id
    case SessionInit(s,cs,of,af) => Json.obj("t"->"welcome","info"->s,"others"->cs,"openFiles"->of,"activeFile"->af)
    case SessionChanged(s) => "session_changed" of s
    case SessionStopped(s) => "session_stopped" of s    
    case FileCreated(f) => "newfile" of f
    case FileDeleted(f) => "rmfile" of f
    case FileId(i) => "file" of i
    case _ => error("couldnt translate")
  }
}