package clide.actors

import akka.actor.Actor
import akka.actor.Identify
import akka.actor.ActorIdentity
import play.api.libs.concurrent.Akka
import play.api.Play.current
import akka.actor.ActorLogging

class Server extends Actor with ActorLogging {  
  import Messages._
  
  private case object Initialize
  
  var users    = context.system.deadLetters
  var projects = context.system.deadLetters  
  
  def receive = {
    case Initialize =>
      context.actorSelection("/user/users")    ! Identify("users")
      context.actorSelection("/user/projects") ! Identify("projects")      
    case ActorIdentity(who,ref) =>
      ref.map(who match {
	    case "users"    => users_=
	    case "projects" => projects_=	    
	  })
    case message: UserServerMessage =>
      log.info("forwarding message to user server")
      users.forward(message)    
    case message: ProjectServerMessage =>
      log.info("forwarding message to project server")
      projects.forward(message)
  }
  
  override def preStart {    
    self ! Initialize
  }
}