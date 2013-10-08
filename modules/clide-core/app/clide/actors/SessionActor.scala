package clide.actors

import akka.actor._
import clide.models._
import clide.Core.DB
import clide.Core.DAL._
import clide.Core.DAL.profile.simple._
import scala.util.Random
import scala.collection.JavaConversions._
import scala.collection.mutable.Map
import scala.slick.session.Session

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
  val openFiles = Map[Long,FileInfo]()  
  val fileServers = Map[Long,ActorRef]()
  
  val colors = context.system.settings.config.getStringList("sessionColors").toSet
  
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
    SessionInfos.update(this.session)
    context.parent ! SessionChanged(this.session)    
    this.session
  }
  
  def switchFile(next: Option[Long]): Boolean = 
    if (next.isEmpty || openFiles.contains(next.get)) DB.withSession { implicit session: Session =>
      this.session = this.session.copy(activeFile = next)
      context.parent ! SessionChanged(this.session)
      peer           ! FileSwitched(this.session.activeFile)
      SessionInfos.update(this.session)      
      true
    } else false
  
  def initializeFile(id: Long) = {
    log.info("initializing file")
    DB.withSession { implicit session: Session => // TODO: Move to File Actors
      FileInfos.get(id).firstOption.fold(peer ! DoesntExist){ info => // TODO: Move to Schema
        context.parent ! WrappedProjectMessage(user,level,WithPath(info.path,OpenFile(this.session)))
      }
    }
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
      openFiles.values.foreach { file => // TODO: Move in ResetFile or so
        fileServers.get(file.id).map(_ ! OpenFile(this.session)).getOrElse {
          context.parent ! WrappedProjectMessage(user,level,WithPath(file.path,OpenFile(this.session)))
        }
      }
    case EnterSession =>
      setActive(true)
      peer = sender
      context.watch(peer)
      peer ! EventSocket(self,"session")
    case LeaveSession | EOF =>
      setActive(false)
      peer = context.system.deadLetters
      context.unwatch(sender) 
    case CloseSession =>
      context.unwatch(peer)
      peer = context.system.deadLetters 
      DB.withSession { implicit session: Session =>
        SessionInfos.delete(this.session)        
      }
      context.parent ! SessionStopped(session)
      context.stop(self)
    case SwitchFile(id) =>
      if (!switchFile(Some(id))) initializeFile(id)      
    case AcknowledgeEdit => // TODO: CONCURRENCY STUFF!!!      
      peer ! AcknowledgeEdit
    case Edited(f,op) =>
      peer ! Edited(f,op)
    case Annotated(f,u,an) =>
      peer ! Annotated(f,u,an)
    case SetColor(value) =>
      session = session.copy(color = value)
      context.parent ! SessionChanged(session)      
    case CloseFile(id) =>
      DB.withSession { implicit session: Session =>
        OpenedFiles.delete(this.session.id,id)
      }
      openFiles.get(id).map { file =>
        fileServers.get(id).map(_ ! EOF)
        peer ! FileClosed(id)
      }.getOrElse {
        peer ! DoesntExist
      }      
      openFiles.remove(id)
      fileServers.remove(id)
      if (session.activeFile == Some(id))
        switchFile(openFiles.keys.headOption)      
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
        peer ! DoesntExist
      }
    case msg @ Annotate(_,_) =>
      session.activeFile.map{ id => 
        fileServers.get(id).map{ ref =>
          log.info("forwarding annotation to ref")
          ref ! msg
        }.getOrElse {
          log.info("forwarding annotation to path")
          context.parent ! WrappedProjectMessage(user,level,WithPath(openFiles(id).path, msg))
        } 
      }.getOrElse {
        peer ! DoesntExist
      }
    case msg @ FileInitFailed(f) =>
      if (session.activeFile == Some(f))
        switchFile(None)
      peer ! msg
    case msg @ OTState(f,s,r) =>
      val of = OpenedFile(f,s,r)
      if (!openFiles.contains(f.id)) {
        DB.withSession { implicit session: Session =>
          OpenedFiles.create(this.session.id, f.id)      
        }
        openFiles += f.id -> f
      }
      fileServers -= f.id
      fileServers += f.id -> sender
      context.watch(sender)
      peer ! FileOpened(of)
      if (!switchFile(Some(f.id)))
        log.error("couldnt switch file")
    case Terminated(ref) =>
      if (ref == peer) {
	    log.info("going idle due to termination")
	    receive(LeaveSession)
      } else {
        fileServers.find(_._2 == ref).map { case (id,_) =>
          log.info(s"file $id failed")          
          receive(CloseFile(id))
        }
      }
    case msg@ChangeProjectUserLevel(_,_) => // HACK: replace with invitation      
      log.info("invite hack")
      context.parent.forward(WrappedProjectMessage(user,level,msg))
  }
  
  override def postStop() = DB.withSession { implicit session: Session =>
    SessionInfos.update(this.session)   
  }
  
  override def preRestart(reason:Throwable, message:Option[Any]){
    log.error(reason, "Unhandled exception for message: {}", message)
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
    openFiles ++= OpenedFiles.get(this.session.id).map(i => i.id -> i).toMap
    collaborators -= this.session
  }
}