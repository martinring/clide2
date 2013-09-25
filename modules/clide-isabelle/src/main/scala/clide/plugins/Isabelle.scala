package clide.plugins

import akka.actor._
import com.typesafe.config.ConfigFactory
import scala.concurrent.duration._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._

object Isabelle extends App {  
  val system = ActorSystem("clide-isabelle",ConfigFactory.load.getConfig("clide-isabelle")) 
  implicit val dispatcher = system.dispatcher
  
  system.actorOf(Props[Isabelle],"plugin") 
}

class Isabelle extends Actor with ActorLogging {
  implicit val dispatcher = context.dispatcher
  
  val config = context.system.settings.config
  
  val username = config.getString("plugin.username")
  val email    = config.getString("plugin.email")
  val password = config.getString("plugin.password")    
  
  var server = context.system.deadLetters
  var peer   = context.system.deadLetters
  
  def login() = {
    log.info("attempting login")
    server ! AnonymousFor(username,Login(password))
  }
  
  def signup() = {
    log.info(s"signing up $username")
    server ! SignUp(username,email,password)
  }
  
  def loggedIn(login: LoginInfo): Receive = {    
    case LoggedOut(user) =>
      log.info("logged out")
      context.system.shutdown()
    case EventSocket(peer) =>
      log.info("connected to backstage session")
      this.peer = peer
  }
  
  def receive = {
    case ActorIdentity("server",None) =>
      log.error("couldn't reach the server")
      context.system.shutdown()
    case ActorIdentity("server",Some(ref)) =>
      server = ref
      log.info("connected to clide")
      login()
    case DoesntExist =>
      log.info(s"user $username hasnt been signed up yet")      
      signup()
    case WrongPassword =>
      log.error(s"user $username is already signed up with different password")
      context.system.shutdown()
    case SignedUp(info) =>
      log.info(s"signed up")
      login()
    case LoggedIn(info, login) => // TODO: UserInfo contains password hash!!!
      log.info(s"logged in")
      context.system.scheduler.scheduleOnce(30 seconds) {
        server ! IdentifiedFor(username,login.key,Logout)
      } 
      server ! IdentifiedFor(username,login.key,StartBackstageSession)
      context.become(loggedIn(login))
  }
  
  override def preStart() = {
    log.info("initializing isabelle plugin")
    val path   = context.system.settings.config.getString("plugin.server-path")
    val server = context.actorSelection(path)
    server ! Identify("server")
  }
}