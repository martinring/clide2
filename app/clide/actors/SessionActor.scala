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
  
  def goIdle() {
    session = session.copy(active = false)
    DB.withSession { implicit s: Session =>
      val q = for (info <- SessionInfos if info.id === id) yield info      
	  q.update(session)
    }
    context.parent ! SessionIdle(session)
  }
       
  def receive = {
    // echoing
    case ProjectJoined(info) =>
      collaborators += info
      peer ! ProjectJoined(info)
    case SessionStopped(info) =>
      collaborators -= info
      peer ! SessionStopped(info)
    case SessionIdle(info) =>
      peer ! SessionIdle(info)
    case StartSession =>
      peer = sender
      context.watch(peer)
      peer ! EventSocket(self)
    case EnterSession =>
      context.parent ! SessionStarted(session,collaborators)
      peer ! SessionStarted(session,collaborators)
    case Terminated(ref) =>
      log.info("going idle due to termination")
      goIdle()
  }
  
  override def preStart() {
    session = id.flatMap { id =>
      val q = for (info <- SessionInfos if info.id === id) yield info
      DB.withSession { implicit session: Session =>
        q.firstOption.map { i =>
          q.update(i.copy(active = true))
          i.copy(active = true)
        }
      }
    }.getOrElse {
      DB.withSession { implicit session: Session =>
        val info = SessionInfo(
          id = None,                
          user = this.user.name,
          project = project.id,
          active = true
        )
        val nid = SessionInfos.autoinc.insert(info)
        this.id = Some(nid)
        val res = info.copy(id = Some(nid))
        context.parent ! SessionCreated(res)
        res
      }
    }        
  }
}