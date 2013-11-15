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
import scala.collection.mutable.Buffer
import scala.concurrent.Future

/**
 * @param owner The Session, this cursor belongs to
 * @param file  The referenced file state
 * @param anchor The position of the cursor
 * @param head Optional value indicating the end of the selected range if something is seleced. This might lie before or after the anchor position.
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
private class Assistant(project: ProjectInfo, createBehavior: AssistantControl => AssistantBehavior) extends Actor with ActorLogging with AssistantControl with Stash {     
  var peer              = context.system.deadLetters  
  var info: SessionInfo = null
  val collaborators     = Set.empty[SessionInfo]
  val files             = Map.empty[Long,OpenedFile]
  val behavior = createBehavior(this)
  val cursors  = Map.empty[Long,Map[Long,Cursor]]
    
  def chat(msg: String, tpe: Option[String] = None) = {
    peer ! Talk(None,msg,tpe)
  }
   
  
  case object Continue
  
  def openFile(path: Seq[String]): Future[OpenedFile] = ???
  
  def annotate(file: OpenedFile, name: String, annotations: Annotations): Unit = 
    peer ! Annotate(file.info.id, file.revision, annotations, name)

  def edit(file: OpenedFile, edit: Operation): Future[Unit] = ???
  
  def stop() = self ! PoisonPill
  
  implicit val ec = context.dispatcher
   
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
          annotations(file) = annotations(file).mapValues(a => Annotations.transform(a, operation).get)          
        
      case Edited(file,operation) =>
        val prev = files(file)
        val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
        files(file) = next
        
        edits(file) = if (edits.isDefinedAt(file))
          Operation.compose(edits(file), operation).get         
        else operation
        
        if (annotations.isDefinedAt(file))
          annotations(file) = annotations(file).mapValues(a => Annotations.transform(a, operation).get)
          
      case Annotated(file,user,as,name) =>
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
        
      case _ => this.stash()
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
        behavior.fileOpened(file)
        behavior.fileActivated(file)
      }         
      
    case FileClosed(file) if files.isDefinedAt(file) =>
      behavior.fileInactivated(files(file))
      behavior.fileClosed(files(file))
      files.remove(file)
      
    case Processed(Edited(file,operation)) if files.isDefinedAt(file) =>      
      val f = Future(behavior.fileChanged(files(file), operation, cursors.get(file).map(_.values.toSeq).getOrElse(Seq.empty)))
      f.onComplete {
        case Success(_) => 
          self ! Continue
        case Failure(e) =>
          log.error("there is a problem with the behavior: {}", e)
          self ! Continue
      }
      context.become(working)           
      
    case Edited(file,operation) if files.isDefinedAt(file) =>      
      val prev = files(file)
      val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
      files(file) = next
      val f = Future(behavior.fileChanged(next, operation, cursors.get(file).map(_.values.toSeq).getOrElse(Seq.empty)))
      f.onComplete {
        case Success(_) => 
          self ! Continue
        case Failure(e) =>
          log.error(e, "there is a problem with the behavior: {}", e.getMessage())
          e.printStackTrace()
          self ! Continue
      }
      context.become(working)
      
    case Annotated(file, user, annotations, name) if files.isDefinedAt(file) =>
      val ps = annotations.positions(AnnotationType.Class,"cursor")      
      if (ps.nonEmpty) for {
        user  <- collaborators.find(_.id == user)
        file  <- files.get(file)
        pos   <- ps
      } {
        if (!cursors.isDefinedAt(file.info.id))
          cursors(file.info.id) = Map.empty
        
        cursors(file.info.id) += user.id -> Cursor(user,file,pos)
        val f = Future(behavior.cursorMoved(Cursor(user,file,pos)))
        f.onComplete {
          case Success(_) => 
            self ! Continue
          case Failure(e) =>
            log.error("there is a problem with the behavior: {}", e)
            self ! Continue
        }
        context.become(working)
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
      Future(behavior.start(project)).onComplete {
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