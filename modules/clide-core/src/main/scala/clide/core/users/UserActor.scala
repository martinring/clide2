package clide.core.users

import akka.actor._
import akka.persistence.EventsourcedProcessor
import scala.collection.mutable.Map
import scala.concurrent.duration._
import clide.core.projects.ProjectRegistry

object UserActor {
  def props(name: String, email: String, password: Array[Byte]) = Props(classOf[UserActor],name,email,password)
  case class LoggedIn(token: String, timeout: Deadline) extends PossiblyHarmful
  // Extending PossiblyHarmful prevents remote actor systems to send instances of this type of message to this
  // actor system. This way, AuthorizedRequest cannot be used externally and should be secure.  
  case class AuthorizedRequest(user: String, id: Long, message: Any) extends PossiblyHarmful
}

class UserActor(name: String, email: String, password: Array[Byte]) extends EventsourcedProcessor {
  val tokens = Map.empty[String, Deadline]
  val projectRegistry = context.actorOf(ProjectRegistry.props(name),"projects")
  
  def receiveRecover = {
    case UserActor.LoggedIn(token: String, timeout: Deadline) =>
      if (timeout.hasTimeLeft) tokens += token -> timeout
      else currentPersistentMessage.foreach { p => deleteMessage(p.sequenceNr) }
  }
  
  def receiveCommand = {
    case Auth.Login(name,pwd) =>
      if (name != name || Hash(pwd+email) != password) sender ! Auth.LoginRefused
      else {
        val token = java.util.UUID.randomUUID().toString()
        val timeout = 1 hour fromNow        
        persist(UserActor.LoggedIn(token,timeout)) { _ =>
          tokens += token -> timeout
          sender ! Auth.LoggedIn(Auth.Token.Full(token))
        }
      }
      
    case Auth.Request(user,Auth.Token.Full(token),id,message) =>
      if (user != name)
        sender ! Auth.Response(id, Auth.AuthenticationRefused)
      else tokens.get(token) match {
        case None => sender ! Auth.Response(id, Auth.AuthenticationRefused)
        case Some(timeout) if timeout.isOverdue => sender ! Auth.Response(id, Auth.AuthenticationTimedOut)
        case _ => projectRegistry.forward(UserActor.AuthorizedRequest(user,id,message))
      }
  }
}
