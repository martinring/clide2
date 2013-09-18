package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._

class SessionActor(
    var id: Option[Long],
    var collaborators: Set[SessionInfo],
    var user: UserInfo,
    var project: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
  
  var session: SessionInfo = null
  var peer = context.system.deadLetters
  var activeFile: Option[Long] = None
  var openFiles = Map[Long,FileInfo]()
          
  def setActive(value: Boolean) = DB.withSession { implicit session: Session =>
    this.session = this.session.copy(active = value)
    val q = for (info <- clide.models.SessionInfos if info.id === id) yield info        
    q.update(this.session)
    this.session
  }
  
  def receive = {
    // echoing
    case SessionChanged(info) => if (info != session) {
      collaborators -= info
      collaborators += info
      peer ! SessionChanged(info)
    }
    case SessionStopped(info) => if (info != session) {
      collaborators -= info
      peer ! SessionStopped(info)
    }
    case RequestSessionInfo =>
      sender ! SessionInit(session,collaborators)
    case EnterSession =>
      setActive(true)
      peer = sender
      context.watch(peer)
      peer ! EventSocket(self)      
      context.parent ! SessionChanged(session)
    case LeaveSession | EOF =>
      setActive(false)
      peer = context.system.deadLetters
      context.unwatch(sender)            
      context.parent ! SessionChanged(session)
    case CloseSession =>
      context.unwatch(peer)
      peer = context.system.deadLetters           
      DB.withSession { implicit session: Session =>
        val q = for (info <- clide.models.SessionInfos if info.id === id) yield info
        q.delete
      }
      context.parent ! SessionStopped(session)
    case Terminated(ref) =>
      log.info("going idle due to termination")
      receive(LeaveSession)
  }
  
  override def preStart() = DB.withSession { implicit session: Session =>
    this.session = id.flatMap { id =>            
      SessionInfos.get(id).map { i =>
        val i_ = i.copy(active = true)
        SessionInfos.update(i_)
        i_
      }      
    }.getOrElse {      
      val res = SessionInfos.create(
        user = this.user.name,
        project = project.id,
        activeFile = activeFile,
        active = true)
      context.parent ! SessionChanged(res)
      res      
    }
    openFiles = OpenFiles.get(this.session.id).map(i => i.id -> i).toMap
    collaborators -= this.session
  }
}