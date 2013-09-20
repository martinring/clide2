package clide.actors

import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.DB
import play.api.Play.current
import akka.actor._
import clide.models._
import clide.actors._
import java.util.UUID
import scala.slick.session.Session
import play.api.Logger

class UserActor(var user: UserInfo) extends Actor with ActorLogging {
  import Messages._
  import Events._
  
  var logins   = Map[String,LoginInfo]()
  var projects = Map[String,ProjectInfo]()
  var otherProjects = Map[ProjectInfo,ProjectAccessLevel.Value]()
  var backstagePeer: Option[ActorRef] = None

  override def preStart() {
    log.info("initializing user actor")    
    logins = DB.withSession { implicit session: Session =>
      LoginInfos.getForUser(user.name).elements.map(l => l.key -> l).toMap
    }
    projects = DB.withSession { implicit session: scala.slick.session.Session =>
      ProjectInfos.byOwner(user.name).map(p => p.name -> p).toMap
    }
    otherProjects = DB.withSession { implicit session: scala.slick.session.Session =>
      ProjectAccessLevels.getUserProjects(user.name).elements.toMap
    }
    log.info("creating project actors")
    projects.foreach { case (name,project) =>
      context.actorOf(Props(classOf[ProjectActor],project),name)
    }
  }
  
  def authenticate(key: String): Either[AuthEvent,LoginInfo] = 
    logins.get(key).toRight(SessionTimedOut) // TODO: Handle Timeouts    
  
  def receive = {
    case Identified(key,msg) => authenticate(key).fold(
        { event => sender ! event },
        { login => (identified(login) orElse anonymous)(msg) })
    case Anonymous(msg) => anonymous(msg)
    case External(user,msg) => (external(user) orElse anonymous)(msg)
    // EVENTS
    case DeletedProject(project) =>
      projects -= project.name
    case Terminated(peer) =>
      backstagePeer = backstagePeer.filter(_ != peer)
  }
  
  def anonymous: Receive = {
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
        context.system.eventStream.publish(LoggedIn(user,login))
      }
    case _ => sender ! NotAllowed
  }
  
  def external(user: UserInfo): Receive = {    
    case _ => sender ! NotAllowed
  }
          
  def identified(login: LoginInfo): Receive = {        
    case Login(password) =>      
      if (UserInfos.passwordHash(user.name, password) != user.password) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else
        sender ! LoggedIn(user, login)
      
    case Logout =>            
      DB.withSession { implicit sesion: Session => LoginInfos.delete(login) }
      logins -= login.key                
      sender ! LoggedOut(user)
      context.system.eventStream.publish(LoggedOut(user))
    
    case CreateProject(name,description) =>
      val project = DB.withSession { implicit session: Session => ProjectInfos.create(name,user.name,description) }
      projects += name -> project      
      context.actorOf(Props(classOf[ProjectActor], project), project.name)
      sender ! CreatedProject(project)
      context.system.eventStream.publish(CreatedProject(project))
    
    case StartBackstageSession =>
      backstagePeer = Some(sender)
      context.watch(sender)
      sender ! EventSocket(self)
      
    case WithProject(name,msg) =>
      projects.get(name) match {
        case Some(project) =>
          context.actorSelection(s"$name").tell(
            WrappedProjectMessage(user, ProjectAccessLevel.Admin,msg),sender)
        case None => sender ! DoesntExist
      } 
     
    case WithUser(name,msg) =>
      Logger.info(s"${user.name} received $msg for $name")
      if (name == user.name) (identified(login) orElse anonymous)(msg)
      else context.actorSelection(s"../$name").tell(External(user,msg),sender)     
      
    case Validate => sender ! Validated(user)
    
    case BrowseProjects => sender ! UserProjectInfos(projects.values.toSet,otherProjects.keySet)
  }
}