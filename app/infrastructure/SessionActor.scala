package infrastructure

import akka.actor.Actor
import models._
import akka.actor.ActorLogging

/**
 * The SessionActor coordinates a client session and provides the 
 * communication interface between the server system and a 
 * generic client.
 * @author Martin Ring <martin.ring@dfki.de>
 */
class SessionActor(user: GenericUser, project: Project) extends Actor with ActorLogging {
  def receive = {
    case msg => println(msg)
  }
  
  override def preStart() {
    log.info(f"session started for ${user.name}")
  }
}