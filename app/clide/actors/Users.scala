package clide.actors

import scala.slick.driver.H2Driver.simple._
import akka.actor.Actor
import play.api.Play.current
import play.api.db.slick.DB
import akka.actor.Props
import akka.actor.ActorLogging
import scala.concurrent.Future

object Users {
  trait Message
  case object Initialize extends Message
  case class SignedUp(user: clide.models.User) extends Message
  case class Deleted(who: String) extends Message
}

class Users extends Actor with ActorLogging {
  import Users._
  import users._
  
  def receive = {
    case Initialize =>
      log.info("creating user actors")
      val users = DB.withSession { implicit session: scala.slick.session.Session =>
        val q = for (user <- clide.models.Users) yield user.* 
        q.elements }
      users.foreach { user => context.actorOf(Props(classOf[User], user), user.name) }
    case SignedUp(user) =>
      context.actorOf(Props(classOf[User],user), user.name)
  }
  
  override def preStart() {
    self ! Initialize
  }
}