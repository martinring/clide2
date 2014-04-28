package clide.core.sessions

import akka.actor._
import clide.core.projects.ProjectInfo
import akka.persistence.EventsourcedProcessor

object SessionActor {
  def props(project: ProjectInfo, projectActor: ActorRef) = Props(classOf[SessionActor], project, projectActor)
}

class SessionActor(project: ProjectInfo, projectActor: ActorRef) extends EventsourcedProcessor with ActorLogging {
  def receiveRecover = {
    case _ =>
  }
  
  def receiveCommand = {
    case _ =>
  }
}