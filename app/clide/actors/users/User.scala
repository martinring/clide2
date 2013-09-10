package clide.actors.users

import akka.actor.Actor
import akka.actor.ActorLogging

object User {
  case object SessionIdle
}

class User(user: clide.models.User) extends Actor with ActorLogging {    
  def receive = {
    case () =>
  }
  
  override def preStart() {
    log.info(f"starting")
  }
}