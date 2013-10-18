package clide.ghc

import akka.actor.Props
import clide.assistants._
import clide.collaboration.Operation
import clide.models._

class GHCAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  def startup() {    
    if (new java.io.File(project.root).mkdirs())
      chat("Created temporary work space")
    chat("I'm ready to go")
    self ! AssistantSession.Activate
  }
  
  def fileAdded(file: OpenedFile) {
    log.info("{}: {}", file.info.path, file.info.mimeType)
    if (file.info.mimeType == Some("text/x-haskell")) { // TODO
      val model = context.actorOf(Props(classOf[HaskellDocumentModel], this.peer, project), "file" + file.info.id)
      registerDocumentModel(file.info.id, model)
    }
  }
  
  def fileChanged(file: OpenedFile, change: Operation, after: OpenedFile) = {
    chat("you changed somthing")
    log.info(change.toString)
  }
  
  def fileClosed(file: OpenedFile) = {
    log.info("file closed")
  }
  
  def shutdown() {
    chat("I'm leaving")
  }
}