package clide.plugins

import com.typesafe.config.Config
import akka.actor._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._

abstract class Assistant extends Actor with ActorLogging {
  def createSession(project: ProjectInfo): ActorRef    
  
  /** May be overridden to modify invitation behaviour **/
  def onInvitation(project: ProjectInfo) = {
    log.info(s"starting session for ${project.owner}/${project.name}")
    val act = createSession(project)
    server.tell(IdentifiedFor(loginInfo.user,loginInfo.key,WithUser(project.owner,WithProject(project.name,StartSession))),act)
    sessions += act
    context.watch(act)
  }
  
  val config   = context.system.settings.config
  
  val username = config.getString("assistant.username")
  val password = config.getString("assistant.password")
  val email    = config.getString("assistant.email")

  var server   = context.system.deadLetters
  var peer     = context.system.deadLetters
  var sessions = Set[ActorRef]()
  var loginInfo: LoginInfo = null
  
  def login() = {
    log.info("attempting login")
    server ! AnonymousFor(username,Login(password))
  }
  
  def signup() = {
    log.info(s"signing up $username")
    server ! SignUp(username,email,password)
  }
  
  def loggedIn: Receive = {    
    case LoggedOut(user) =>
      loginInfo = null
      context.unbecome()
      log.info("logged out")
      context.system.shutdown()
    case EventSocket(peer,"backstage") =>
      log.info("connected to backstage session")
      this.peer = peer
      log.info("requesting project infos")
      peer ! BrowseProjects
    case UserProjectInfos(own,other) =>
      log.info("received project infos")
      (own ++ other).foreach(onInvitation)
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
      server ! IdentifiedFor(username,login.key,StartBackstageSession)
      loginInfo = login
      context.become(loggedIn)    
  }
  
  override def preStart = {
    log.info(s"starting assistant '$username'")
    val path   = config.getString("assistant.server-path")
    val server = context.actorSelection(path)
    server ! Identify("server")
  }  
}