/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */
package clide.actors

import akka.actor._
import clide.models._
import scala.util.Random
import scala.collection.JavaConversions._
import scala.collection.mutable.Map
import scala.slick.session.Session
import clide.actors.Messages._
import clide.actors.Events._
import clide.persistence.DBAccess
import scala.concurrent.duration._
/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private object SessionActor {
  def props(
    id: Option[Long],
    collaborators: Set[SessionInfo],
    user: UserInfo,
    project: ProjectInfo,
    isHuman: Boolean,
    eventHistory: List[BroadcastEvent])(implicit dbAccess: DBAccess) =
      Props(classOf[SessionActor], id, collaborators, user, project, isHuman, eventHistory, dbAccess)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class SessionActor(
    var id: Option[Long],
    var collaborators: Set[SessionInfo],
    val user: UserInfo,
    val project: ProjectInfo,
    val isHuman: Boolean,
    var eventHistory: List[BroadcastEvent])
    (implicit val dbAccess: DBAccess) extends Actor with ActorLogging{
  import dbAccess.schema._
  import dbAccess.{db => DB}

  val level = ProjectAccessLevel.Admin // TODO
  var session: SessionInfo = null
  var peer = context.system.deadLetters
  val openFiles = Map.empty[Long,FileInfo]
  val fileServers = Map.empty[Long,ActorRef]

  val activityTimeouts = Map.empty[Long,Cancellable]
  
  import context.dispatcher
      
  def indicateActivity(file: Long) {
    if (isHuman) {
      if (activityTimeouts.isDefinedAt(file)) {
        activityTimeouts.get(file).foreach(_.cancel)          
      } else {
        log.info("indicating activity")
        context.parent ! BroadcastEvent(session.id, System.currentTimeMillis, WorkingOnFile(file))  
      }
      activityTimeouts(file) = context.system.scheduler.scheduleOnce(1.second) {
        log.info("indicating inactivity")
        context.parent ! BroadcastEvent(session.id, System.currentTimeMillis, DoneWithFile(file))
        activityTimeouts.remove(file)
      }
    }
  }
  
  val colors = context.system.settings.config.getStringList("sessionColors").toSet

  def wrap(msg: ProjectMessage) = Messages.internal.WrappedProjectMessage(user,isHuman,level,msg)
  
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

  def initializeFile(id: Long) = {
    if (fileServers.contains(id))
      fileServers(id) ! EOF
    log.info("initializing file")
    DB.withSession { implicit session: Session => // TODO: Move to File Actors
      FileInfos.get(id).fold(peer ! DoesntExist){ info => // TODO: Move to Schema
        log.info("forwarding openfile to path")
        context.parent ! wrap(WithPath(info.path,Messages.internal.OpenFile(this.session)))
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
          collaborators,
          eventHistory)
      openFiles.values.foreach { file => // TODO: Move in ResetFile or so
        fileServers.get(file.id).map(_ ! Messages.internal.OpenFile(this.session)).getOrElse {
          context.parent ! wrap(WithPath(file.path,Messages.internal.OpenFile(this.session)))
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
    case OpenFile(id) =>
      initializeFile(id)
    case AcknowledgeEdit(f) =>
      indicateActivity(f)
      peer ! AcknowledgeEdit(f)
    case Edited(f,op) =>
      peer ! Edited(f,op)      
    case Annotated(f,u,an,n) =>
      peer ! Annotated(f,u,an,n)
    case msg@AnnotationsClosed(f,u,n) =>
      peer ! msg
    case SetColor(value) =>
      session = session.copy(color = value)
      context.parent ! SessionChanged(session)
    case msg: BroadcastMessage if sender == peer =>
      context.parent ! BroadcastEvent(session.id, System.currentTimeMillis, msg)
    case e: BroadcastEvent =>
      eventHistory = e :: eventHistory
      peer ! e
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
    case msg @ Edit(id,_,_) =>
      fileServers.get(id).map{ ref =>
        ref ! msg
      } getOrElse {        
        context.parent ! wrap(WithPath(openFiles(id).path, msg))
      }      
    case msg @ Annotate(id,_,_,_) =>
      fileServers.get(id).map{ ref =>
        ref ! msg
      } getOrElse {        
        context.parent ! wrap(WithPath(openFiles(id).path, msg))
      }
    case msg @ SubscribeToAnnotations(id,_,_) =>
      fileServers.get(id).map { ref =>
        ref ! msg        
      } getOrElse {        
        context.parent ! wrap(WithPath(openFiles(id).path, msg))
      }
    case msg @ UnsubscribeFromAnnotations(id,_,_) =>
      fileServers.get(id).map { ref =>
        ref ! msg        
      } getOrElse {        
        context.parent ! wrap(WithPath(openFiles(id).path, msg))
      }
    case msg @ FileInitFailed(f) =>
      peer ! msg
    case msg @ Events.internal.OTState(f,s,r) =>
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
    case msg@Kick(id) =>
      context.parent.forward(wrap(msg))
    case msg@ChangeProjectUserLevel(_,_) => // HACK: replace with invitation
      context.parent.forward(wrap(msg))
    case Kicked =>
      peer ! Kicked
      receive(CloseSession)
  }

  override def postStop() = DB.withSession { implicit session: Session =>    
    SessionInfos.update(this.session.copy(active = false))
  }

  override def preRestart(reason:Throwable, message:Option[Any]){
    log.error(reason, "Unhandled exception for message: {}", message)
  }

  override def preStart() = DB.withSession { implicit session: Session =>
    this.session = id.flatMap { id => SessionInfos.get(id)
    }.getOrElse {
      val res = SessionInfos.create(
        user = this.user.name,
        color = randomColor(),
        project = project.id,
        isHuman = this.isHuman,
        active = false)
      context.parent ! SessionChanged(res)
      res
    }
    openFiles ++= OpenedFiles.get(this.session.id).map(i => i.id -> i).toMap
    collaborators -= this.session
  }
}
