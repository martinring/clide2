package infrastructure

import akka.actor.Actor
import models._
import akka.actor.ActorLogging
import akka.actor.PoisonPill
import akka.actor.Scheduler
import play.api.Play.current
import scala.concurrent.duration._
import java.io.File

/**
 * The SessionActor coordinates a client session and provides the 
 * communication interface between the server system and a 
 * generic client.
 * @author Martin Ring <martin.ring@dfki.de>
 */
class SessionActor(user: GenericUser, project: Project) extends Actor with ActorLogging {
  import Messages._
  def receive = {
    case CloseSession =>      
      context.stop(self)
  }
  
  override def preStart() {
    log.info(f"session started for ${user.name}")
  }
  
  override def postStop() {
    log.info(f"session closed (${user.name})")
  }
}