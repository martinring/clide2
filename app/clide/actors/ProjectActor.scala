package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._
import clide.actors.files._

class ProjectActor(var info: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
    
  var user: UserInfo = null
  var root: ActorRef     = context.system.deadLetters
  var sessions = Set[SessionInfo]()
  var sessionActors = Map[Long,ActorRef]() 
  
  def admin: Receive = {
    case DeleteProject =>
      DB.withSession { implicit session: Session =>
        ProjectInfos.delete(info.id)
      }
      sender         ! DeletedProject(info)
      context.parent ! DeletedProject(info)
      context.stop(self)
    case StartSession =>
      sessions.find { session =>
        session.user == user.name &&
        !session.active        
      }.map { session =>
        sessionActors.get(session.id.get).getOrElse {
          context.actorOf(Props(classOf[SessionActor],session.id,sessions,user,this.info))
        }
      }.getOrElse {
        context.actorOf(Props(classOf[SessionActor],None,sessions,user,this.info))
      }.forward(StartSession)
  }
  
  def write: Receive = {
    case StartFileBrowser =>
      val browser = context.actorOf(Props(classOf[FileBrowser],true,root))
      browser.forward(StartFileBrowser)
  }
  
  def read: Receive = {
    case StartFileBrowser =>
      val browser = context.actorOf(Props(classOf[FileBrowser],false,root))
      browser.forward(StartFileBrowser)
  }
  
  def none: Receive = {
    case _ => sender ! NotAllowed
  }
  
  def receive = {
    case SessionIdle(info) =>
      val old = sessions.find(_.id == info.id)
      old.map { sessions -= _ }
      sessions += info
    case msg@SessionStarted(info,_) =>      
      sessionActors.values.foreach(_.forward(ProjectJoined(info)))
      sessions += info
      sessionActors += info.id.get -> sender
    case SessionIdle(info) =>
      log.info("idle " + info)
      val old = sessions.find(_.id == info.id)
      old.map { sessions -= _ }
      sessions += info
      sessionActors.values.foreach(_.forward(SessionIdle(info)))
    case SessionStopped(info) =>
      sessions -= info
      sessionActors -= info.id.get
      sessionActors.values.foreach(_.forward(SessionStopped(info)))
    case WrappedProjectMessage(user,level,msg) =>
      this.user = user
      level match {
        case ProjectAccessLevel.Admin =>
          (admin orElse write orElse read orElse none)(msg)
        case ProjectAccessLevel.Write =>
          (write orElse read orElse none)(msg)
        case ProjectAccessLevel.Read =>
          (read orElse none)(msg)
        case _ =>
          none(msg)
      }
  }
  
  override def preStart() {
    root = context.actorOf(Props(classOf[FolderActor], info, None, "files"),"files")    
    sessions = DB.withSession { implicit session =>
      val q = for (session <- SessionInfos if session.projectId === info.id) yield session      
      q.elements.toSet
    }    
    log.info(s"project ${info.owner}/${info.name}")
  }
}