package clide.actors

import akka.actor.Actor
import akka.actor.Identify
import akka.actor.ActorIdentity
import play.api.libs.concurrent.Akka
import play.api.Play.current

object Server {
  var instance = Akka.system.deadLetters
  
  case object Initialize
}

class Server extends Actor {
  import Server._
  
  var users    = context.system.deadLetters
  var projects = context.system.deadLetters
  var files    = context.system.deadLetters
  
  def receive = {
    case Initialize =>
      context.actorSelection("../users")    ! Identify("users")
      context.actorSelection("../projects") ! Identify("projects")
      context.actorSelection("../files")    ! Identify("files")
    case ActorIdentity(who,ref) =>
      ref.map(who match {
	    case "users"    => users_=
	    case "projects" => projects_=
	    case "files"    => files_=
	  })
    case message: Users.Message =>
      users.forward(message)
    case message: Projects.Message =>
      projects.forward(message)
    case message: Files.Message =>
      files.forward(message)
  }
  
  override def preStart {
    self ! Initialize
  }
}