package clide.actors.projects

import akka.actor.Actor
import akka.actor.ActorLogging
import clide.models.ProjectInfo
import clide.models.ProjectAccessInfos

object ProjectActor {
  trait Message
  case object Delete extends Message
}

class ProjectActor(project: ProjectInfo) extends Actor with ActorLogging {    
  def receive = {
    case () =>
  }
  
  override def preStart() {
    ProjectAccessInfos.    
    log.info("started")
  }
}