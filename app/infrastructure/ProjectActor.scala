package infrastructure

import akka.actor.Actor

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ProjectActor extends Actor {
  def receive = {
    case _ =>
  }
}

object ProjectActor {
  sealed trait ProjectRequest  
    
  sealed trait ProjectReply
  
}