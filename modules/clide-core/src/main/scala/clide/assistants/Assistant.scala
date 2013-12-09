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

package clide.assistants

import akka.actor._
import clide.models._
import clide.actors.Events._
import clide.actors.Messages.{RequestSessionInfo,IdentifiedFor,WithUser,Talk}
import clide.collaboration.{Annotations,Operation,Document,AnnotationType}
import scala.collection.mutable.Map
import scala.collection.mutable.Set
import scala.concurrent.Future
import clide.actors.Messages._
import scala.util.Success
import scala.util.Failure
import scala.collection.mutable.Buffer
import scala.concurrent.Future
import scala.language.postfixOps
import scala.concurrent.Await
import scala.concurrent.duration._

/**
 * @param owner The Session, this cursor belongs to
 * @param file  The referenced file state
 * @param anchor The position of the cursor
 * @param head Optional value indicating the end of the selected range if something is seleced. This might be before or after the anchor position.
 * @todo head is not implemented right now
 * @author Martin Ring <martin.ring@dfki.de>
 */
case class Cursor(owner: SessionInfo, file: OpenedFile, anchor: Int, head: Option[Int] = None) {
  override def equals(other: Any) = other match {
    case c: Cursor if c.owner == this.owner && c.file == this.file => true
    case _ => false
  }
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class Assistant(project: ProjectInfo, createBehavior: AssistantControl => AssistBehavior) extends Actor with ActorLogging with AssistantControl with Stash {
  var peer              = context.system.deadLetters
  var info: SessionInfo = null
  val collaborators     = Set.empty[SessionInfo]
  val files             = Map.empty[Long,OpenedFile]
  val behavior = createBehavior(this)
  val cursors  = Map.empty[Long,Map[Long,Cursor]]
  val config = context.system.settings.config
  val assistantName             = config.getString("assistant.username")
  val receiveOwnChatMessages    = config.getBoolean("assistant.receiveOwnChatMessages")
  val automaticWorkingIndicator = config.getBoolean("assistant.automaticWorkingIndicator")
  val automaticFailureIndicator = config.getBoolean("assistant.automaticFailureIndicator")
  val workIndicatorDelay = Duration(config.getMilliseconds("assistant.workIndicatorDelay"), MILLISECONDS)

  def chat(msg: String, tpe: Option[String] = None) = {
    peer ! Talk(None,msg,tpe)
  }


  case object Continue  
  
  def openFile(path: Seq[String]): Future[OpenedFile] = ???

  def annotate(file: OpenedFile, name: String, annotations: Annotations): Unit =
    peer ! Annotate(file.info.id, file.revision, annotations, name)

  def edit(file: OpenedFile, edit: Operation): Future[Unit] = ???

  val workStates: Map[Long, Boolean] = Map.empty.withDefaultValue(false)
  val workTimeouts: Map[Long, Cancellable] = Map.empty 
  
  def workOnFile(file: OpenedFile): Unit = workOnFile(file.info.id)
  
  def workOnFile(file: Long): Unit = {
    if (workIndicatorDelay.length > 0) {
	  if (workStates(file))
	    workTimeouts.get(file).foreach(_.cancel())
	  else context.system.scheduler.scheduleOnce(workIndicatorDelay){ () =>
	    workStates(file) = true
	    peer ! WorkingOnFile(file)
	  }
    } else {
      peer ! WorkingOnFile(file)
    }    
  }
  
  def doneWithFile(file: OpenedFile): Unit = doneWithFile(file.info.id)
  
  def doneWithFile(file: Long): Unit = {
    if (workIndicatorDelay.length > 0) {
      if (workStates(file) == false)
        workTimeouts.get(file).foreach(_.cancel())
      else context.system.scheduler.scheduleOnce(workIndicatorDelay){ () =>
        workStates(file) = false
        peer ! DoneWithFile(file)
      }
    } else{
      peer ! DoneWithFile(file)
    }
  }
  
  def failedInFile(file: OpenedFile, message: Option[String]): Unit = failedInFile(file.info.id, message)
  
  def failedInFile(file: Long, message: Option[String]): Unit = peer ! FailureInFile(file, message)
  
  def stop() = self ! PoisonPill

  implicit val executionContext = context.dispatcher

  case class Processed(e: Event)

  def working: Receive = {
    val edits:       Map[Long,Operation] = Map.empty
    val annotations: Map[Long,scala.collection.Map[(Long,String),Annotations]] = Map.empty

    {
      case Processed(Edited(file,operation)) =>
        edits(file) = if (edits.isDefinedAt(file))
          Operation.compose(edits(file), operation).get
        else operation

        if (annotations.isDefinedAt(file))
          annotations(file) = annotations(file).mapValues(_ transform operation get)

      case Edited(file,operation) if files.isDefinedAt(file) =>
        val prev = files(file)
        val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
        files(file) = next

        edits(file) = if (edits.isDefinedAt(file))
          Operation.compose(edits(file), operation).get
        else operation

        if (annotations.isDefinedAt(file))
          annotations(file) = annotations(file).mapValues(_ transform operation get)

      case Annotated(file,user,as,name) if files.isDefinedAt(file) =>
        if (annotations.isDefinedAt(file))
          annotations(file) += (user,name) -> as

      case Continue =>
        unstashAll()

        context.become(initialized)
        for {
          (file, op) <- edits
        } self ! Processed(Edited(file,op))
        for {
          (file,as) <- annotations
          ((user,name),as) <- as
        } self ! Annotated(file,user,as,name)
        
      case Terminated(_) =>
        log.warning("peer terminated")
        context.stop(self)        
        
      case _ => this.stash()      
    }
  }
  
  def doWork(file: Option[Long])(task: Future[Unit]) {
    // can be forced to block for tiny computations with Future.sucessfull
    if (!task.isCompleted) {
      if (automaticWorkingIndicator) file.foreach(workOnFile(_))
      context.become(working)
      task.onComplete {
        case Success(_) => 
          self ! Continue
          if (automaticWorkingIndicator) file.foreach(doneWithFile(_))
        case Failure(e) =>
          log.error(e, "there is a problem with the behavior")
          self ! Continue
          if (automaticFailureIndicator) file.foreach(failedInFile(_,Some(e.getMessage())))
          
      }
    }
  }

  def initialized: Receive = {
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      log.debug("file opened: {}", info)
      if (files.isDefinedAt(info.id)) {
        log.warning("file info has been renewed from server: {} (at revision {})", info, revision)
        files(info.id) = file
      } else if (behavior.mimeTypes.intersect(file.info.mimeType.toSet).nonEmpty) {
        files(info.id) = file
        doWork(Some(info.id))(for {
          _ <- behavior.fileOpened(file)
          _ <- behavior.fileActivated(file)
        } yield())
      }

    case FileClosed(file) if files.isDefinedAt(file) =>
      val f = files(file)
      files.remove(file)
      doWork(None)(for {
        _ <- behavior.fileInactivated(f)
        _ <- behavior.fileClosed(f)
      } yield ())

    case Processed(Edited(file,operation)) if files.isDefinedAt(file) =>
      doWork(Some(file))(behavior.fileChanged(files(file), operation, cursors.get(file).map(_.values.toSeq).getOrElse(Seq.empty)))      

    case Edited(file,operation) if files.isDefinedAt(file) =>
      val prev = files(file)
      val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
      files(file) = next
      doWork(Some(file))(behavior.fileChanged(next, operation, cursors.get(file).map(_.values.toSeq).getOrElse(Seq.empty)))    
    
    case BroadcastEvent(who, when, Talk(to, msg, tpe)) if (who != info.id || receiveOwnChatMessages) =>
      doWork(None)(behavior.receiveChatMessage(collaborators.find(_.id == who).get,msg,tpe,when))
      
    case SessionChanged(session) =>
      val existing = collaborators.find(_.id == session.id)
      existing match {
        case Some(old) => 
          collaborators.remove(old)
          // TODO: Handle sesion changes
          if (!old.active && session.active)
            doWork(None)(behavior.collaboratorJoined(session))
          if (old.active && !session.active)
            doWork(None)(behavior.collaboratorLeft(session))
          collaborators.add(session)
        case None =>
          collaborators.add(session)
          if (session.active)
            doWork(None)(behavior.collaboratorJoined(session))
      }      
      
    case SessionStopped(session) =>      
      collaborators.filter(_.id != session.id)
      behavior.collaboratorLeft(session)

    case Annotated(file, user, annotations, name) if files.isDefinedAt(file) =>
      // TODO: More universal approach on cursor positions etc.
      val ps = annotations.positions(AnnotationType.Class,"cursor")
      if (ps.nonEmpty) for {
        user  <- collaborators.find(_.id == user)
        file  <- files.get(file)
        pos   <- ps
      } {
        if (!cursors.isDefinedAt(file.info.id))
          cursors(file.info.id) = Map.empty

        cursors(file.info.id) += user.id -> Cursor(user,file,pos)
        doWork(Some(file.info.id))(behavior.cursorMoved(Cursor(user,file,pos)))
      }

    case BroadcastEvent(who, when, LookingAtFile(file)) =>
      for (who <- collaborators.find(_.id == who) if who.isHuman) {
        log.debug("{} is looking at file {}", who.user, file)
        if (!files.contains(file))
          peer ! OpenFile(file)
      }
      
    case Terminated(_) => context.stop(self)
  }

  private case object Initialized
  private case class  InitializationFailed(cause: Throwable)

  def receive = {
    case EventSocket(ref,"session") =>
      log.debug("session started")
      peer = ref
      context.watch(peer)
      behavior.start(project).onComplete {
        case Success(()) => self ! Initialized
        case Failure(e)  => self ! InitializationFailed(e)
      }

    case Initialized =>
      log.debug("requesting session info")
      peer ! RequestSessionInfo

    case InitializationFailed(e) =>
      context.stop(self)

    case SessionInit(info, collaborators, conversation) =>
      log.debug("session info received")
      this.info = info
      this.collaborators ++= collaborators
      context.become(initialized)
    
    case Terminated(_) => context.stop(self)
  }

  override def postStop() {
    Await.ready(behavior.stop, 1.minute)
  }
}
