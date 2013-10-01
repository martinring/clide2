package clide.plugins

import akka.actor._
import clide.models._
import clide.actors.Events._
import clide.actors.Messages.{RequestSessionInfo,SwitchFile,IdentifiedFor,WithUser}
import clide.collaboration._

abstract class AssistantSession(project: ProjectInfo) extends Actor with ActorLogging {
  var peer              = context.system.deadLetters
  var activeFiles       = Map[Long,Long]()
  var info: SessionInfo = null
  var collaborators     = Set[SessionInfo]()
  var files             = Map[Long,OpenedFile]()
  
  def fileAdded(file: OpenedFile)
  def fileChanged(file: OpenedFile, change: Operation, after: OpenedFile)
  def fileClosed(file: OpenedFile)
   
  def annotate(file: OpenedFile, annotations: Annotations) = {
    peer ! clide.actors.Messages.Annotate(file.revision, annotations)
  }
  
  def startup() { }
  
  def shutdown() { }
  
  def receive = {    
    case EventSocket(ref,"session") =>
      log.info("session started")
      peer = ref
      log.info("requesting session info")
      peer ! RequestSessionInfo
    case SessionInit(info, collaborators) =>
      log.info("session info received")
      this.info = info
      this.collaborators = collaborators  
      collaborators.foreach { info =>
        if (info.active && info.activeFile.isDefined) {
          log.info(s"${info.user} is looking at ${info.activeFile.get}")
          activeFiles += info.id -> info.activeFile.get
        }
      }
      activeFiles.values.toSeq.distinct.foreach { id =>
        peer ! SwitchFile(id)
      }
      startup()
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      files += info.id -> file
      fileAdded(file)
    case FileClosed(file) =>
      fileClosed(files(file))
      files -= file
    case Edited(file,operation) =>
      val prev = files(file)
      val next = OpenedFile(prev.info,new Document(prev.state).apply(operation).get.content, prev.revision + 1)
      files += file -> next
      fileChanged(prev, operation, next)
    case SessionChanged(info) =>
      if (info.active && info.activeFile.isDefined) {
        log.info(s"${info.user} is looking at ${info.activeFile.get}")
        activeFiles += info.id -> info.activeFile.get
        peer ! SwitchFile(info.activeFile.get)
      } else {
        log.info(s"${info.user} is inactive")
        activeFiles -= info.id
      }
  }
  
  override def postStop() {
    shutdown()
  }
}