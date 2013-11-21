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
import clide.actors.files._
import scala.collection.mutable.Buffer
import scala.slick.session.Session
import org.h2.jdbc.JdbcSQLException
import clide.persistence.DBAccess

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private object ProjectActor {
  def apply(info: ProjectInfo)(implicit dbAccess: DBAccess) =
    Props(classOf[ProjectActor], info, dbAccess)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class ProjectActor(var info: ProjectInfo)(implicit val dbAccess: DBAccess) extends Actor with ActorLogging {
  import dbAccess.schema._
  import dbAccess.{db => DB}
  import clide.actors.Messages.internal._
  import clide.actors.Messages._
  import clide.actors.Events._

  var user: UserInfo = null
  var level = ProjectAccessLevel.None
  var root: ActorRef     = context.system.deadLetters

  var sessions      = Set.empty[SessionInfo]
  var sessionActors = Map.empty[Long,ActorRef]

  // TODO: Persist
  var conversationHistory = Buffer.empty[Talked]

  def admin: Receive = {
    case DeleteProject =>
      DB.withSession { implicit session: Session =>
        ProjectInfos.delete(info.id)
      }
      sender         ! DeletedProject(info)
      context.parent ! DeletedProject(info)
      // TODO: Very important: The Event has to be forwarded to the collaborators
      // somehow! This is currently a bug!
      context.stop(self)

    case ChangeProjectUserLevel(user,level) =>
      try { DB.withSession { implicit session: Session =>
        ProjectAccessLevels.change(info.id, user, level)
        sessionActors.values.foreach(_ ! ChangedProjectUserLevel(info, user, level))
        context.parent ! ChangedProjectUserLevel(info, user, level)
      } } catch {
        case e: JdbcSQLException =>
          sender ! DoesntExist
      }
  }

  def write: Receive = {
    case StartFileBrowser =>
      val browser = context.actorOf(FileBrowser(true,root))
      browser.forward(StartFileBrowser)
    case StartSession =>
      sessions.find { session =>
        session.user == user.name &&
        !session.active
      }.map { session =>
        sessionActors.get(session.id).getOrElse {
          context.actorOf(SessionActor.props(Some(session.id),sessions,user,this.info,conversationHistory.toVector))
        }
      }.getOrElse {
        context.actorOf(SessionActor.props(None,sessions,user,this.info,conversationHistory.toVector))
      }.forward(EnterSession)
    case msg @ WithPath(_,_: FileWriteMessage) =>
      root.forward(msg)
  }

  def read: Receive = {
    case StartFileBrowser =>
      val browser = context.actorOf(FileBrowser(false,root))
      browser.forward(StartFileBrowser)
    case msg @ WithPath(_,_: FileReadMessage) =>
      root.forward(msg)
    case Talk(None,what,t) =>
      val talked = Talked(user.name, what, t, System.currentTimeMillis)
      conversationHistory.append(talked)
      sessionActors.values.foreach(_ ! talked)
    case Talk(Some(sess),what,t) =>
      log.warning("not supported yet")
      sessionActors.get(sess).map(_ ! Talked(user.name, what, t, System.currentTimeMillis))
  }

  def none: Receive = {
    case _ => sender ! NotAllowed
  }

  def receive = {
    case msg@SessionChanged(info) =>
      if (!info.active && sessions.exists(i =>
        i.id != info.id && i.user == info.user && !i.active))
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

  override def preRestart(reason:Throwable, message:Option[Any]){
    log.error(reason, "Unhandled exception for message: {}", message)
  }

  override def preStart() {
    root = context.actorOf(FolderActor.props(info, None, "files"),"files")
    sessions = DB.withSession { implicit session =>
      SessionInfos.getForProject(info.id).toSet
      // TODO: Clean up unused sessions again
    }
    log.info(s"project ${info.owner}/${info.name}")
  }
}
