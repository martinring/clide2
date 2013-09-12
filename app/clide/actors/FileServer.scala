package clide.actors

import akka.actor._
import clide.models._
import clide.actors.files.FolderActor
import clide.actors.files.FileEventSource

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
}

class FileServer extends Actor with ActorLogging {
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
    case event: FileEventSource.FileEvent =>
      log.info(event.toString())
  }
}