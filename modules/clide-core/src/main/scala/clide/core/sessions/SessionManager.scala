/*package clide.core.sessions

import akka.actor._
import clide.core.projects.ProjectInfo
import akka.persistence.EventsourcedProcessor

object SessionManager {
  def props(project: ProjectInfo, projectActor: ActorRef) = Props(classOf[SessionManager], project, projectActor)
}

class SessionManager(project: ProjectInfo, projectActor: ActorRef) extends EventsourcedProcessor with ActorLogging {
  def receiveRecover = {
    case _ =>
  }

  def receiveCommand = {
    case _ =>
  }
}*/
