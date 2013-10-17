package clide.actors

import clide.models._
import akka.actor.ActorRef
import clide.collaboration.Operation
import clide.collaboration.Annotations

object Events {
  trait Event  
  case object TimeOut extends Event
  case object UnexpectedTermination extends Event
  
  case class FileInitFailed(file: Long) extends Event
    
  case class EventSocket(in: ActorRef, id: String) extends Event
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
  case class ProjectCouldNotBeCreated(reason: String) extends ProjectEvent
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent
  case class ChangedProjectUserLevel(project: ProjectInfo, user: String, level: ProjectAccessLevel.Value) extends ProjectEvent
      
  trait SessionEvent extends Event  
  case class SessionInit(
      info: SessionInfo, 
      collaborators: Set[SessionInfo],
      conversation: List[Talked]) extends SessionEvent
  case class SessionChanged(info: SessionInfo) extends SessionEvent
  case class SessionStopped(info: SessionInfo) extends SessionEvent  
  case class FileSwitched(id: Option[Long]) extends SessionEvent
  case class FileClosed(id: Long) extends SessionEvent
  case class FileOpened(file: OpenedFile) extends SessionEvent
  case class Edited(file: Long, op: Operation) extends SessionEvent
  case class Annotated(file: Long, user: Long, an: Annotations, name: String) extends SessionEvent
  case object AcknowledgeEdit extends SessionEvent
  case object AcknowledgeAnnotation extends SessionEvent
  case class Talked(from: String, msg: String, timestamp: Long) extends SessionEvent
  case class OTState(info: FileInfo, content: String, revision: Long) extends SessionEvent
  
  case class UserProjectInfos(
      userProjects: Set[ProjectInfo],
      collaborating: Set[ProjectInfo]) extends Event        
}