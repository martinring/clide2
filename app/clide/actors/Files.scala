package clide.actors

import akka.actor.Actor
import clide.models.ProjectInfo

object Files {
  trait Message
  case class Query(project: ProjectInfo, path: Seq[String])   
}

class Files extends Actor {
  import Files._
  
  def receive = {
    case Query(project, path) =>
      context.actorSelection("")
  }
}