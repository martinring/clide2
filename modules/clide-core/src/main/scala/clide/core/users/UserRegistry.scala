package clide.core.users

import akka.persistence.EventsourcedProcessor
import scala.collection.mutable.Map
import akka.actor._

object UserRegistry {
  def props = Props[UserRegistry]()
  case class SignedUp(name: String, email: String, hash: Array[Byte])
}

class UserRegistry extends EventsourcedProcessor with ActorLogging {
  import Auth._
  
  val users = Map.empty[String,ActorRef]  

  def receiveRecover = {
    case msg @ UserRegistry.SignedUp(name,email,password) =>
      users += name -> context.actorOf(UserActor.props(name,email,password),name)
  }
  
  def receiveCommand = {    
    case msg @ SignUp(UserInfo(name,email), password: String) =>      
      if (!name.matches("[a-zA-Z0-9_]+")) sender ! SignUpRefused(SignUpRefused.InvalidName)
      else if (password.length < 8)       sender ! SignUpRefused(SignUpRefused.InvalidPassword)
      else if (users.contains(name))      sender ! SignUpRefused(SignUpRefused.NameNotUnique)      
      persist(UserRegistry.SignedUp(name,email,Hash(password+email))) { msg =>
        val actor = context.actorOf(UserActor.props(msg.name, msg.email, msg.hash),msg.name)
        users += msg.name -> actor
        sender ! SignedUp(UserInfo(msg.name,msg.email))
      }
      
    case msg @ Login(name, pwd) =>
      users.get(name) match {
        case None => sender ! LoginRefused
        case Some(actor) => actor.forward(msg)
      }
      
    case msg : Request =>
      users.get(msg.username) match {
        case None => sender ! Response(msg.id, AuthenticationRefused)
        case Some(actor) => actor.forward(msg)
      }
  }
}