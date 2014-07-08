package clide.core.users

import akka.actor._
import akka.persistence._
import scala.concurrent.duration._
import scala.concurrent.duration.Duration.Infinite
import scala.language.postfixOps

object User {
  def props(name: String, email: String, password: Array[Byte], isHuman: Boolean) = 
    Props(classOf[User],name,email,password,isHuman)
}

class User(val name: String, var email: String, var passwordHash: Array[Byte], isHuman: Boolean) extends PersistentActor with ActorLogging {
  import clide.messages.users.User._
  import clide.messages.users.Auth._
  
  val persistenceId = s"user-$name"
  
  val logins = collection.mutable.Map.empty[String,ActorRef]
  
  override def preStart {
    context.setReceiveTimeout(1 hour)
  }
  
  def receiveCommand = {
    {
      case Login(`name`,password) =>
        if (Security.hash(email, password) == passwordHash) {
          val client = sender
          persist(LoggedIn(AuthenticationToken.Full(name, Security.newToken))) { msg =>
            context.become(loggedIn(msg.token.key))
            client ! msg
          }
        } else {
          sender ! LoginRefused
        }
    }
  }
  
  def loggedIn(token: String): Receive = {
    context.setReceiveTimeout(1 hour)
    
    {
      case Login(`name`,password) =>
        if (Security.hash(email,password) == passwordHash) {
          val client = sender
          persist(LoggedIn(AuthenticationToken.Full(name, Security.newToken))) { msg =>
            context.become(loggedIn(msg.token.key))
            client ! msg
          }
        } else {
          sender ! LoginRefused
        }    
  
      case Request(AuthenticationToken.Full(`name`,`token`), Logout) =>
        context.become(receiveCommand)
        
      case ReceiveTimeout =>
        context.become(receiveCommand)
    }
  }
  
  def receiveRecover = {
    case LoggedIn(AuthenticationToken.Full(`name`, token)) =>
      context.become(loggedIn(token))
  }
}