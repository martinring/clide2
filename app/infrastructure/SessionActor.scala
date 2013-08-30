package infrastructure

import akka.actor.Actor
import models._

/**
 * The SessionActor coordinates a client session and provides the 
 * communication interface between the server system and a 
 * generic client.
 * @author Martin Ring <martin.ring@dfki.de>
 */
class SessionActor(project: Project, user: GenericUser) extends Actor {
  def receive = {
    case msg => println(msg)
  }
}

object SessionActor {
  sealed trait SessionRequest
  
  sealed trait SessionReply
  
}