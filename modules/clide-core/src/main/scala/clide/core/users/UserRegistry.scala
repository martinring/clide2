package clide.core.users

import akka.persistence.PersistentActor
import scala.collection.mutable.Map
import akka.actor._
import scala.collection.mutable.Buffer

object UserRegistry {
  def props = Props[UserRegistry]()
  
  object Events {
    case class SignedUp(name: String, email: String, hash: Array[Byte], isHuman: Boolean)
  }  
}

class UserRegistry extends PersistentActor with ActorLogging {  
  import clide.messages.users.Auth._

  val persistenceId = "users"
  
  val users = Map.empty[String,ActorRef]    

  def receiveRecover = {
    case msg @ UserRegistry.Events.SignedUp(name,email,password,isHuman) =>
      users += name -> context.actorOf(User.props(name,email,password,isHuman))
  }

  def receiveCommand = {
    case SignUp(name,email,password,isHuman) =>
      val client = sender

      val errors = Buffer.empty[SignUpRefused.Reason]

      if (!Security.namingPattern.pattern.matcher(name).matches()) 
        errors += SignUpRefused.InvalidName        
      if (password.length < Security.minimumPasswordLength)
        errors += SignUpRefused.InvalidPassword
      if (users.contains(name))
        errors += SignUpRefused.NameNotUnique           
      
      if (errors.nonEmpty)
        client ! SignUpRefused(errors.toSeq)
      else persist(UserRegistry.Events.SignedUp(name,email,Security.hash(email,password),isHuman)) { msg =>        
        users += msg.name -> context.actorOf(User.props(name, email, msg.hash,isHuman))
        client ! SignedUp(msg.name,msg.email)
      }
  }
}