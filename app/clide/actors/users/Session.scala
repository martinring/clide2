package clide.actors.users

import akka.actor.Actor
import clide.models.GenericUser
import clide.models.ProjectInfo
import akka.actor.Terminated
import akka.actor.ActorLogging

object Session {
  case object Initialize
}

class Session(project: ProjectInfo, user: GenericUser) extends Actor with ActorLogging {
  import Session._
  
  /** identifies the connected peer actor **/
  var peer = context.system.deadLetters  
  
  def receive = {
    case Initialize =>
      peer = sender
      context.watch(peer)
    case Terminated(peer) =>
      log.info("peer terminated")
      context.parent ! User.SessionIdle
  }
}