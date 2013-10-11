package clide.plugins

import akka.actor._
import clide.models._
import clide.actors.Events._
import clide.actors.Messages.{RequestSessionInfo,SwitchFile,IdentifiedFor,WithUser,Talk}
import clide.collaboration._
import scala.collection.mutable._

object AssistantSession {
  case object Activate
}

abstract class AssistantSession(project: ProjectInfo) extends Actor with ActorLogging {
  import AssistantSession._ 
  
  var documentModels    = Map[Long,ActorRef]()
  var peer              = context.system.deadLetters
  val activeFiles       = Map[Long,Long]()
  var info: SessionInfo = null
  val collaborators     = Set[SessionInfo]()
  val files             = Map[Long,OpenedFile]()
  
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
      if (info.active && info.activeFile.isDefined) {
        log.info(s"${info.user} is looking at ${info.activeFile.get}")
        activeFiles(info.id) = info.activeFile.get
        peer ! SwitchFile(info.activeFile.get)
      } else {
        log.info(s"${info.user} is inactive")
        activeFiles.remove(info.id)
      }    
  }
    
  def receive = {
    case EventSocket(ref,"session") =>
      log.info("session started")
      peer = ref
      startup()
    
    case Activate =>
      log.info("requesting session info")
      peer ! RequestSessionInfo
      
    case SessionInit(info, collaborators) =>
      log.info("session info received")
      this.info = info
      this.collaborators ++= collaborators  
      collaborators.foreach { info =>
        if (info.active && info.activeFile.isDefined) {
          log.info(s"${info.user} is looking at ${info.activeFile.get}")
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