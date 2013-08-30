package infrastructure

import akka.actor.Actor
import models._
import akka.actor.ActorRef
import akka.actor.Props
import akka.actor.ActorLogging

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ProjectActor(project: Project) extends Actor with ActorLogging {
  import Messages._
  def receive = {
    case OpenSession(user,project) =>      
      sender ! Welcome(context.actorOf(Props(new SessionActor(user,project))))
  }
  
  override def preStart {
    log.info("project actor started")
  }
}