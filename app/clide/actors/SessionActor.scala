package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._
import scala.util.Random
import scala.collection.JavaConversions._

class SessionActor(
    var id: Option[Long],
    var collaborators: Set[SessionInfo],
    var user: UserInfo,    
    var project: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
  
  val level = ProjectAccessLevel.Admin // TODO
  var session: SessionInfo = null
  var peer = context.system.deadLetters
  var openFiles = Map[Long,FileInfo]()  
  var fileServers = Map[Long,ActorRef]()
  
  val colors = current.configuration.getStringList("clide.sessionColors").get.toSet
  
  def randomColor(): String = {
    var remaining = colors
    collaborators.foreach(remaining -= _.color)
    if (remaining.size > 0)
      remaining.toSeq(Random.nextInt(remaining.size))
    else
      colors.toSeq(Random.nextInt(colors.size))
  }
          
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
      sender ! SessionInit(
          session,
          collaborators)
      openFiles.values.foreach { file =>
        fileServers.get(file.id).map(_ ! OpenFile).getOrElse {
          context.parent ! WrappedProjectMessage(user,level,WithPath(file.path,OpenFile))
        }
      }
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
    case SwitchFile(id) => if (session.activeFile != Some(id)) {
      log.info("open file")
      session = session.copy(activeFile = Some(id))
      if (openFiles.contains(id)) {        
        peer ! FileSwitched(session.activeFile)
        
      } else {
        DB.withSession { implicit session: Session => 
          FileInfos.get(id).firstOption.map { info =>
            context.parent ! WrappedProjectMessage(user,level,WithPath(info.path,OpenFile))
          } 
        }        
      }
      context.parent ! SessionChanged(session)
    }
    case AcknowledgeEdit => // TODO: CONCURRENCY STUFF!!!
      session.activeFile.map(fileServers += _ -> sender)
      peer ! AcknowledgeEdit
    case Edited(f,op) =>     
      peer ! Edited(f,op)
    case CloseFile(id) =>
      openFiles.get(id).map { file =>
        fileServers.get(id).map(_ ! EOF)
        peer ! FileClosed(id)
      }.getOrElse {
        peer ! DoesntExist
      }
      DB.withSession { implicit session: Session =>
        OpenedFiles.delete(this.session.id,id)
      }
      openFiles -= id
      fileServers -= id
      if (session.activeFile.map(_ == id).getOrElse(false)) {
        session.copy(activeFile = openFiles.keys.headOption)
        peer ! FileSwitched(session.activeFile)
        context.parent ! SessionChanged(session)
      }
    case msg @ Edit(_,_) =>      
      session.activeFile.map{ id => 
        fileServers.get(id).map{ ref =>
          log.info("forwarding edit to ref")
          ref ! msg
        }.getOrElse {
          log.info("forwarding edit to path")
          context.parent ! WrappedProjectMessage(user,level,WithPath(openFiles(id).path, msg))
        } 
      }.getOrElse {
        sender ! DoesntExist
      }
    case msg @ OTState(f,s,r) =>
      val of = OpenedFile(f,s,r)
      if (!openFiles.contains(f.id)) {
        DB.withSession { implicit session: Session =>
          OpenedFiles.create(this.session.id, f.id)      
        }
        openFiles += f.id -> f
      }              
      fileServers += f.id -> sender      
      peer ! FileOpened(of)
      if (session.activeFile == Some(f.id))
        peer ! FileSwitched(session.activeFile)
    case Terminated(ref) =>
      log.info("going idle due to termination")
      receive(LeaveSession)
  }
  
  override def postStop() = DB.withSession { implicit session: Session =>
    SessionInfos.update(this.session)   
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
        color = randomColor(),
        project = project.id,
        activeFile = None,
        active = true)
      context.parent ! SessionChanged(res)
      res      
    }
    openFiles = OpenedFiles.get(this.session.id).map(i => i.id -> i).toMap
    collaborators -= this.session
  }
}