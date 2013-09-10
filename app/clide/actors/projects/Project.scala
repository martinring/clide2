package clide.actors.projects

import akka.actor.Actor
import akka.actor.ActorLogging
import clide.models.ProjectInfo

object Project {
  
}

class Project(project: ProjectInfo) extends Actor with ActorLogging {    
  def receive = {
    case () =>
  }
  
  override def preStart() {
    log.info(f"starting")
  }
}