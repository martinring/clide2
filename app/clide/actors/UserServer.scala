package clide.actors

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import play.api.Play.current
import akka.actor.Actor
import akka.actor.Props
import akka.actor.ActorLogging
import scala.concurrent.Future
import clide.models._
import play.api.libs.Crypto

object UserServer {
  trait Message
  case object Initialize extends Message
  case class SignUp(name: String, email: String, password: String) extends Message
  case class Login(name: String, password: String) extends Message
  case class Logout(name: String, password: String) extends Message
  
  trait UserEvent
  case class SignedUp(user: UserInfo) extends UserEvent
  case class LoggedIn(user: UserInfo) extends UserEvent
  case class LoggedOut(user: UserInfo) extends UserEvent
  case class NotFound(name: String) extends UserEvent
  case class WrongPassword(user: UserInfo) extends UserEvent
}

class UserServer extends Actor with ActorLogging {
  import UserServer._
  import users._    
  
  def receive = {    
    case SignUp(name,email,password) =>
      val user = UserInfo(name,email,UserInfos.passwordHash(name, password),None,None)
      DB.withSession { implicit session: scala.slick.session.Session => UserInfos.insert(user) }
      context.actorOf(Props(classOf[UserActor],user), user.name)
      sender ! SignedUp(user)
      context.parent ! SignedUp(user)
    case msg @ Login(name,_) =>
      context.child(name) match {
        case None => sender ! NotFound(name)
        case Some(ref) => ref.forward(msg)
      }
  }
  
  override def preStart() {
    log.info("creating user actors")
    val users = DB.withSession { implicit session: scala.slick.session.Session =>
      val q = for (user <- UserInfos) yield user.* 
      q.elements }
    users.foreach { user => context.actorOf(Props(classOf[UserActor], user), user.name) }
  }
}