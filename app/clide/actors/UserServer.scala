package clide.actors

import scala.slick.driver.H2Driver.simple._
import akka.actor.Actor
import play.api.Play.current
import play.api.db.slick.DB
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
}

class UserServer extends Actor with ActorLogging {
  import UserServer._
  import users._
  
  def receive = {    
    case SignUp(name,email,password) =>
      DB.withSession { implicit session: scala.slick.session.Session =>
        val user = UserInfo(name,email,Crypto.sign(name+password),None,None)        
        UserInfos.insert(user)
        context.actorOf(Props(classOf[User],user), user.name)
        Seq(sender,context.parent).foreach(_ ! SignedUp(user))             
      }
    case Login(name,password) =>
      DB.withSession { implicit session: scala.slick.session.Session =>
        
      }
  }
  
  override def preStart() {
    log.info("creating user actors")
    val users = DB.withSession { implicit session: scala.slick.session.Session =>
      val q = for (user <- UserInfos) yield user.* 
      q.elements }
    users.foreach { user => context.actorOf(Props(classOf[User], user), user.name) }
  }
}