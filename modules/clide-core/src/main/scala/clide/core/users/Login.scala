package clide.core.users

import akka.actor._
import akka.persistence.PersistentActor
import scala.concurrent.duration._
import scala.language.postfixOps
import clide.messages.users.Auth.Logout

object Login {
  def props(user: ActorRef) = Props(classOf[Login], user)  
  val timeout = 3 days
}

class Login(user: ActorRef, token: String) extends Actor with ActorLogging {
  override def preStart {
    context.setReceiveTimeout(Login.timeout)
  }
  
  def receive = {
    case Logout => 
      self ! PoisonPill
  }
}