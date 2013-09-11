package clide.actors

import akka.actor.Actor
import clide.models.ProjectInfo
import clide.actors.files.Folder
import akka.actor.Props
import akka.actor.ActorRef

object Files {
  trait Message  
  case class Query(project: ProjectInfo, path: Seq[String])
}

class Files extends Actor {
  import Files._
  
  def projectRootActor(project: ProjectInfo): ActorRef = {
    context.child(project.actorName) match {
      case Some(ref) => ref
      case None      => context.actorOf(Props(classOf[Folder], project.root), project.actorName)
    }
  }
  
  def receive = {
    case msg @ Query(project, path) =>
      projectRootActor(project).forward(msg)
  }
}