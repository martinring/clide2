package clide.actors.users

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import play.api.Play.current
import akka.actor.Actor
import akka.actor.ActorLogging
import clide.models._
import java.util.UUID
import scala.slick.session.Session

object UserActor {
  case object SessionIdle
}

class UserActor(var user: UserInfo) extends Actor with ActorLogging {
  import clide.actors.UserServer._
  
  def receive = {
    case Login(name, password) =>
      if (name != user.name)
        log.warning(f"Not responsible for $name")
      else if (UserInfos.passwordHash(name, password) != user.password)
        sender ! WrongPassword
      else {
        user = user.copy(
          session = Some(UUID.randomUUID().toString())
        )
        DB.withSession { implicit Session: Session => UserInfos.getByName(name).update(user) }
        sender ! LoggedIn(user)
      }         
  }   
}