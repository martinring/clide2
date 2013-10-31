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
import clide.collaboration._
import scala.collection.mutable._

/**
 * The companion to the abstract `AssistantSession` convenience class contains
 * the messages, that are specific to this actor.
 */
object AssistantSession {
  /**
   * Must be sent to `self` in the startup method, to indicate, that the session
   * can begin gathering information about the active files, collaborators and 
   * so on
   */
  case object Activate
  
  /**
   * Can be sent to an instance of AssistantSession from anywhere to trigger it
   * to shut down. 
   */
  case object Close
}

abstract class AssistantSession(project: ProjectInfo) extends Actor with ActorLogging {
  import AssistantSession._ 
  
  private var documentModels    = Map[Long,ActorRef]()
  private var peer_              = context.system.deadLetters
  private val activeFiles       = Map[Long,Long]()
  private var info: SessionInfo = null
  private val collaborators     = Set[SessionInfo]()
  private val files             = Map[Long,OpenedFile]()
  def peer = peer_
  
  /**
   * this method must be implemented by subclasses. You should initialize everything
   * you need here. It will be executed before everything else which means, that you
   * can.
   * 
   * `startup` shall never be called directly!
   */
  def startup()
  def fileAdded(file: OpenedFile)
  def fileClosed(file: OpenedFile)
  def shutdown()
  
  def chat(msg: String) = {
    peer ! Talk(None,msg)
  }
  
  private var state = 0
      
  def registerDocumentModel(file: Long, model: ActorRef) {
    files.get(file).fold(sys.error("registered file doesn't exist")){ f =>
      documentModels(file) = model
      context.watch(model)
      model ! DocumentModel.Init(f)
    }   
  }
  
  def initialized: Receive = {
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      log.info("file opened: {}", info)
      if (files.isDefinedAt(info.id)) {
        files(info.id) = file
        documentModels.get(info.id).foreach(_ ! DocumentModel.Init(file))             
      } else {
        files(info.id) = file
        fileAdded(file)        
      }
      
    case FileClosed(file) =>
      fileClosed(files(file))
      files.remove(file)
      documentModels.get(file).foreach(_ ! DocumentModel.Close)
      
    case Edited(file,operation) =>      
      val prev = files(file)
      val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
      files(file) = next
      documentModels.get(file).foreach(_ ! DocumentModel.Change(operation))
      
    case SessionChanged(info) =>
      log.info("session changed: {}", info)
      if (info.active && info.activeFile.isDefined && !files.contains(info.activeFile.get)) {        
        activeFiles(info.id) = info.activeFile.get
        peer ! SwitchFile(info.activeFile.get)
      } else {        
        activeFiles.remove(info.id)
      }    
  }
      
  def receive = {
    case EventSocket(ref,"session") =>
      log.info("session started")
      peer_ = ref
      startup()
    
    case Activate =>
      log.info("requesting session info")
      peer ! RequestSessionInfo
      
    case SessionInit(info, collaborators, conversation) =>
      log.info("session info received")
      this.info = info
      this.collaborators ++= collaborators  
      collaborators.foreach { info =>
        if (info.active && info.activeFile.isDefined) {
          activeFiles += info.id -> info.activeFile.get
      } }
      activeFiles.values.toSeq.distinct.foreach { id =>
        peer ! SwitchFile(id)
      }
      context.become(initialized)
  }
  
  override def postStop() {
    shutdown()
  }
}