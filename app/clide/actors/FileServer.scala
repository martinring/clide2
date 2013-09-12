package clide.actors

import akka.actor.Actor
import clide.models.ProjectInfo
import clide.actors.files.FolderActor
import akka.actor.Props
import akka.actor.ActorRef

object FileServer {
  trait Message
  
  /** Can be used to execute a file query at a specific path **/
  case class WithProject(project: ProjectInfo, action: WithPath) extends Message
  case class WithPath(path: Seq[String], action: FileQuery) extends Message
  
  trait FileQuery
  case object Open       extends FileQuery
  case object Browse     extends FileQuery
  case object Delete     extends FileQuery
  case object Save       extends FileQuery  
  
  trait FileEvent
  case class FileCreated(project: ProjectInfo, path: Seq[String]) extends FileEvent
  case class FileDeleted(project: ProjectInfo, path: Seq[String]) extends FileEvent
  case class FolderCreated(project: ProjectInfo, path: Seq[String]) extends FileEvent
  case class FolderDeleted(project: ProjectInfo, path: Seq[String]) extends FileEvent
}

class FileServer extends Actor {
  import FileServer._
  
  def projectRootActor(project: ProjectInfo): ActorRef = {
    context.child(project.actorName) match {
      case Some(ref) => ref
      case None      => context.actorOf(Props(classOf[FolderActor], project.root), project.actorName)
    }
  }
  
  def receive = {
    case WithProject(project, msg) =>
      projectRootActor(project).forward(msg)    
  }
}