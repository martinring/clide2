 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.assistants

import akka.actor._
import clide.models._
import clide.actors.Events._
import clide.actors.Messages.{RequestSessionInfo,SwitchFile,IdentifiedFor,WithUser,Talk}
import clide.collaboration.{Annotations,Operation,Document,AnnotationType}
import scala.collection.mutable.Map
import scala.collection.mutable.Set
import scala.concurrent.Future
import clide.actors.Messages._
import scala.util.Success
import scala.util.Failure

private class Assistant(project: ProjectInfo, createBehavior: AssistantControl => AssistantBehavior) extends Actor with ActorLogging with AssistantControl {     
  var peer              = context.system.deadLetters  
  var info: SessionInfo = null
  val collaborators     = Set[SessionInfo]()
  val files             = Map[Long,OpenedFile]()
  val behavior = createBehavior(this)    
     
  def chat(msg: String, tpe: Option[String] = None) = {
    peer ! Talk(None,msg,tpe)
  }
   
  private case class Forward(msg: Message)
  
  def openFile(path: Seq[String]): Future[OpenedFile] = ???
  
  def annotate(file: OpenedFile, name: String, annotations: Annotations): Unit = 
    peer ! Annotate(file.info.id, file.revision, annotations, name)

  def edit(file: OpenedFile, edit: Operation): Future[Unit] = ???
  
  def stop() = self ! PoisonPill
  
  private var state = 0
      
  def initialized: Receive = {
    case Forward(msg) =>
      peer ! msg
    
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      log.debug("file opened: {}", info)
      if (files.isDefinedAt(info.id)) {
        log.warning("file info has been renewed from server: {} (at revision {})", info, revision)
        files(info.id) = file
      } else if (behavior.mimeTypes.intersect(file.info.mimeType.toSet).nonEmpty) {
        files(info.id) = file
        behavior.fileOpened(file)
        behavior.fileActivated(file)
      }         
      
    case FileClosed(file) if files.isDefinedAt(file) =>
      behavior.fileInactivated(files(file))
      behavior.fileClosed(files(file))
      files.remove(file)
      
    case Edited(file,operation) if files.isDefinedAt(file) =>      
      val prev = files(file)
      val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
      files(file) = next
      behavior.fileChanged(next, operation)
      
    case Annotated(file, user, annotations, name) if files.isDefinedAt(file) =>
      val ps = annotations.positions(AnnotationType.Class,"cursor")
      if (ps.nonEmpty) for {
        user  <- collaborators.find(_.id == user)
        pos   <- ps
      } {
        behavior.cursorMoved(files(file), user, pos)
      }
      
    case SessionChanged(info) =>
      log.debug("session changed: {}", info)
      if (info.active && info.activeFile.isDefined && !files.contains(info.activeFile.get)) {
        peer ! OpenFile(info.activeFile.get)
      }
  }
      
  private case object Initialized
  private case class  InitializationFailed(cause: Throwable)  
  
  def receive = {
    case EventSocket(ref,"session") =>
      log.debug("session started")
      peer = ref
      implicit val ec = context.dispatcher
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
      collaborators.foreach { info =>
        if (info.active && info.activeFile.isDefined) {
          peer ! OpenFile(info.activeFile.get)
      } }
      context.become(initialized)
  }
  
  override def postStop() {
    behavior.stop
  }
}