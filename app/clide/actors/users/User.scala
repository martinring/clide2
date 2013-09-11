package clide.actors.users

import akka.actor.Actor
import akka.actor.ActorLogging
import clide.models._

object User {
  case object SessionIdle
}

class User(user: UserInfo) extends Actor with ActorLogging {    
  def receive = {
    case () =>
  }
  
  override def preStart() {
    log.info(f"starting")
  }
}