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

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private object SessionActor {
  def props(
    id: Option[Long],
    collaborators: Set[SessionInfo],
    user: UserInfo,
    project: ProjectInfo,
    conversation: Vector[Talked])(implicit dbAccess: DBAccess) =
      Props(classOf[SessionActor], id, collaborators, user, project, conversation, dbAccess)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class SessionActor(
    var id: Option[Long],
    var collaborators: Set[SessionInfo],
    var user: UserInfo,
    var project: ProjectInfo,
    var conversation: Vector[Talked])
    (implicit val dbAccess: DBAccess) extends Actor with ActorLogging{
  import dbAccess.schema._
  import dbAccess.{db => DB}

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
      FileInfos.get(id).fold(peer ! DoesntExist){ info => // TODO: Move to Schema
        log.info("forwarding openfile to path")
        context.parent ! Messages.internal.WrappedProjectMessage(user,level,WithPath(info.path,Messages.internal.OpenFile(this.session)))
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
          conversation.toList)
      openFiles.values.foreach { file => // TODO: Move in ResetFile or so
        fileServers.get(file.id).map(_ ! Messages.internal.OpenFile(this.session)).getOrElse {
          context.parent ! Messages.internal.WrappedProjectMessage(user,level,WithPath(file.path,Messages.internal.OpenFile(this.session)))
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
    case OpenFile(id) =>
      if (!openFiles.contains(id)) initializeFile(id)
    case AcknowledgeEdit(f) =>
      peer ! AcknowledgeEdit(f)
    case Edited(f,op) =>
      peer ! Edited(f,op)
    case Annotated(f,u,an,n) =>
      peer ! Annotated(f,u,an,n)
    case SetColor(value) =>
      session = session.copy(color = value)
      context.parent ! SessionChanged(session)
    case msg @ Talk(_,_,_) =>
      context.parent ! Messages.internal.WrappedProjectMessage(user,level,msg)
    case msg @ Talked(_,_,_,_) =>
      conversation :+= msg
      peer ! msg
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
    case msg @ Edit(id,_,_) =>
      fileServers.get(id).map{ ref =>
        ref ! msg
      } getOrElse {
        log.info("forwarding edit to path")
        context.parent ! Messages.internal.WrappedProjectMessage(user,level,WithPath(openFiles(id).path, msg))
      }
    case msg @ Annotate(id,_,_,_) =>
      fileServers.get(id).map{ ref =>
        ref ! msg
      } getOrElse {
        log.info("forwarding annotation to path")
        context.parent ! Messages.internal.WrappedProjectMessage(user,level,WithPath(openFiles(id).path, msg))
      }
    case msg @ FileInitFailed(f) =>
      if (session.activeFile == Some(f))
        switchFile(None)
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
      context.parent.forward(Messages.internal.WrappedProjectMessage(user,level,msg))
  }

  override def postStop() = DB.withSession { implicit session: Session =>    
    SessionInfos.update(this.session.copy(active = false))
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
