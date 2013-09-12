package clide.actors.users

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import play.api.Play.current
import akka.actor.Actor
import akka.actor.ActorLogging
import clide.models._
import clide.actors._
import java.util.UUID
import scala.slick.session.Session

object UserActor {
  trait Message

}

class UserActor(var user: UserInfo) extends Actor with ActorLogging {
  import Messages._
  import Events._
  
  var logins = Map[String,LoginInfo]()
  
  def authenticated(key: String)(block: LoginInfo => Unit) =
    logins.get(key).map(block).getOrElse { sender ! NotLoggedIn }
  
  def receive = {
    case Login(password) =>      
      if (UserInfos.passwordHash(user.name, password) != user.password) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else {
        val key   = UUID.randomUUID().toString()
        val login = LoginInfo(user.name,key,None) // TODO: Handle Timeouts!
        DB.withSession { implicit Session: Session => LoginInfos.insert(login) }
        logins += key -> login
        sender ! LoggedIn(user, login)
        context.parent ! LoggedIn(user, login)
      }
    case Logout(key) => authenticated(key) { info =>
      DB.withSession { implicit sesion: Session => LoginInfos.getForKey(key).delete }
      sender ! LoggedOut(user)
      context.parent ! LoggedOut(user)
    }
    case Validate(key) => authenticated(key) { info => sender ! Validated(user,info) }
  }
  
  override def preStart() {
    log.info("initializing user actor")
    DB.withSession { implicit session: Session =>
      logins = LoginInfos.getForUser(user.name).elements.map(l => l.key -> l).toMap
    }
  }
}