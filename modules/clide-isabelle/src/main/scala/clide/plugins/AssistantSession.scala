package clide.plugins

import akka.actor._
import clide.models._
import clide.actors.Events._
import clide.actors.Messages.{RequestSessionInfo,SwitchFile,IdentifiedFor,WithUser}
import clide.collaboration._

abstract class AssistantSession(project: ProjectInfo) extends Actor with ActorLogging {
  var peer = context.system.deadLetters
  var activeFiles = Map[Long,Long]()
  var info: SessionInfo = null
  var collaborators = Set[SessionInfo]()
  var files = Map[Long,OpenedFile]()
  
  def processFile(file: OpenedFile): Option[Annotations]  
  def processFileChange(before: OpenedFile, change: Operation, after: OpenedFile): Option[Annotations] = processFile(after)  
    
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
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      for {
        as <- processFile(file)
      } peer ! clide.actors.Messages.Annotate(revision,as)      
      log.info(file.toString)
      files += info.id -> file
    case Edited(file,operation) =>
      log.info(file.toString + ": " + operation)
      files.get(file).map { case file@OpenedFile(info,content,revision) =>        
        val next = OpenedFile(info,new Document(content).apply(operation).get.content,revision + 1)
        files += file.info.id -> next
        for {
          as <- processFileChange(file, operation, next)
        } peer ! clide.actors.Messages.Annotate(next.revision,as)        
      }    
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
}