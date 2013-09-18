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
  var level = ProjectAccessLevel.None
  var root: ActorRef     = context.system.deadLetters
  
  var sessions      = Set[SessionInfo]()
  var sessionActors = Map[Long,ActorRef]() 
       
  def admin: Receive = {
    case DeleteProject =>
      DB.withSession { implicit session: Session =>
        ProjectInfos.delete(info.id)
      }
      sender         ! DeletedProject(info)
      context.parent ! DeletedProject(info)
      context.stop(self)
  }
  
  def write: Receive = {
    case StartFileBrowser =>
      val browser = context.actorOf(Props(classOf[FileBrowser],true,root))
      browser.forward(StartFileBrowser)
    case StartSession =>
      sessions.find { session =>
        session.user == user.name &&
        !session.active        
      }.map { session =>
        sessionActors.get(session.id).getOrElse {
          context.actorOf(Props(classOf[SessionActor],Some(session.id),sessions,user,this.info))
        }
      }.getOrElse {
        context.actorOf(Props(classOf[SessionActor],None,sessions,user,this.info))
      }.forward(EnterSession)
    case msg @ WithPath(_,OpenFile) =>
      log.info("open file")
      root.forward(msg)
    case msg @ WithPath(_,Edit(_,_)) =>
      log.info("edit file")
      root.forward(msg)
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
    case msg@SessionChanged(info) =>
      if (!info.active && sessions.exists(i =>
        i.id != info.id && i.user == info.user && i.active == false))
        sender ! CloseSession
      sessions -= info
      sessions += info      
      sessionActors += info.id -> sender   
      sessionActors.values.foreach(_.forward(msg))
    case msg@SessionStopped(info) =>
      sessions -= info
      sessionActors -= info.id
      sessionActors.values.foreach(_.forward(msg))
    case WrappedProjectMessage(user,level,msg) =>
      this.user = user
      this.level = level
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
      val u = for (session <- clide.models.SessionInfos if session.projectId === info.id) yield session.active
      u.update(false)
      val q = for (session <- clide.models.SessionInfos if session.projectId === info.id) yield session      
      val r = q.elements.toSet
      r.map(_.user).map { user =>
        val redundant = r.filter(_.user == user)
        if (redundant.size > 1) redundant.tail.foreach { info =>
          val q = for (session <- clide.models.SessionInfos if session.id === info.id) yield session
          q.delete
        }
        redundant.head
      }
    }    
    log.info(s"project ${info.owner}/${info.name}")
  }
}