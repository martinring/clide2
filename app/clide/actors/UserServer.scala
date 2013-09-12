package clide.actors

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import play.api.Play.current
import akka.actor._
import scala.concurrent.Future
import clide.models._
import play.api.libs.Crypto

class UserServer extends Actor with ActorLogging {
  import Messages._
  import Events._
  import users._    
  
  var logins = Map[String,ActorRef]()
  
  def receive = {    
    case SignUp(name,email,password) =>
      val user = UserInfo(name,email,UserInfos.passwordHash(name, password))
      DB.withSession { implicit session: scala.slick.session.Session => UserInfos.insert(user) }
      context.actorOf(Props(classOf[UserActor],user), user.name)
      sender ! SignedUp(user)
      context.parent ! SignedUp(user)
    case WithUser(name, msg) =>
      context.child(name) match {
        case None      => sender ! DoesntExist(name)
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