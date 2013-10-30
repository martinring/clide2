 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors

import akka.actor._
import clide.models._
import clide.Core.DB
import clide.Core.DAL._
import clide.Core.DAL.profile.simple._
import clide.actors.files._
import scala.collection.mutable.Buffer
import scala.slick.session.Session
import org.h2.jdbc.JdbcSQLException

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private object ProjectActor {
  def apply(info: ProjectInfo) = 
    Props(classOf[ProjectActor], info)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class ProjectActor(var info: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
    
  var user: UserInfo = null
  var level = ProjectAccessLevel.None
  var root: ActorRef     = context.system.deadLetters
    
  var sessions      = Set[SessionInfo]()
  var sessionActors = Map[Long,ActorRef]() 
  
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
          context.actorOf(SessionActor(Some(session.id),sessions,user,this.info,conversationHistory.toVector))
        }
      }.getOrElse {
        context.actorOf(SessionActor(None,sessions,user,this.info,conversationHistory.toVector))
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
    case Talk(None,what) =>
      val talked = Talked(user.name, what, System.currentTimeMillis)
      conversationHistory.append(talked)
      sessionActors.values.foreach(_ ! talked)
    case Talk(Some(sess),what) =>      
      log.warning("not supported yet")
      sessionActors.get(sess).map(_ ! Talked(user.name, what,System.currentTimeMillis))
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
    root = context.actorOf(FolderActor(info, None, "files"),"files")    
    sessions = DB.withSession { implicit session => // TODO: Move to Schema
      val u = for (session <- SessionInfos if session.projectId === info.id) yield session.active
      u.update(false)
      val q = for (session <- SessionInfos if session.projectId === info.id) yield session
      val r = q.elements.toSet
      r.map(_.user).map { user =>
        val redundant = r.filter(_.user == user)
        if (redundant.size > 1) redundant.tail.foreach { info =>
          val q = for (session <- SessionInfos if session.id === info.id) yield session
          q.delete
        }
        redundant.head
      }
    }    
    log.info(s"project ${info.owner}/${info.name}")
  }
}