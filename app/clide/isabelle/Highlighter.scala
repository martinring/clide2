package clide.isabelle

import akka.actor.Actor

class Highlighter extends Actor {
  def receive = {
    case _ =>
  }
  
  override def preStart() = {
    context.actorSelection("/user/users") ! 
      SignUp("isabelle","isabelle@clide.informatik.uni-bremen.de","password") // TODO: Move password to config
  }
}