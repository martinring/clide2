package clide.actors

import akka.actor.Actor
import akka.actor.Identify
import akka.actor.ActorIdentity
import play.api.libs.concurrent.Akka
import play.api.Play.current
import akka.actor.ActorLogging

object Server {
  
}

class Server extends Actor with ActorLogging {  
  import Server._
  
  private case object Initialize
  
  var users    = context.system.deadLetters
  var projects = context.system.deadLetters
  var files    = context.system.deadLetters
  
  def receive = {
    case Initialize =>
      context.actorSelection("/user/users")    ! Identify("users")
      context.actorSelection("/user/projects") ! Identify("projects")
      context.actorSelection("/user/files")    ! Identify("files")
    case ActorIdentity(who,ref) =>
      ref.map(who match {
	    case "users"    => users_=
	    case "projects" => projects_=
	    case "files"    => files_=
	  })
    case message: UserServer.Message =>
      log.info("forwarding message to user server")
      users.forward(message)
    case message: ProjectServer.Message =>
      log.info("forwarding message to project server")
      projects.forward(message)
    case message: FileServer.Message =>
      log.info("forwarding message to file server")
      files.forward(message)
  }
  
  override def preStart {    
    self ! Initialize
  }
}