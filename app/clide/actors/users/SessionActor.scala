package clide.actors.users

import akka.actor.Actor
import clide.models.GenericUser
import clide.models.ProjectInfo
import akka.actor.Terminated
import akka.actor.ActorLogging

object SessionActor {
  case object Initialize
}

class SessionActor(project: ProjectInfo, user: GenericUser) extends Actor with ActorLogging {
  import SessionActor._
  
  /** identifies the connected peer actor **/
  var peer = context.system.deadLetters  
  
  def receive = {
    case Initialize =>
      peer = sender
      context.watch(peer)
    case Terminated(peer) =>
      log.info("peer terminated")
      context.parent ! UserActor.SessionIdle
  }
}