package clide.plugins

import clide.models._
import clide.collaboration._
import akka.actor.Props

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._      
     
  var session: Session = null    
  
  def startup() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))    
    session.commands_changed += (context.self ! _)
    session.phase_changed += { p => p match {
      case Session.Startup  => log.info("starting isabelle session")
      case Session.Shutdown => log.info("shutting down isabelle session")
      case Session.Inactive => log.info("isabelle session is inactive")
      case Session.Failed   => log.info("isabelle session failed")
      case Session.Ready    => log.info("isabelle session ready")
                               self ! AssistantSession.Activate
    } }
    session.start(List("HOL"))
  }
  
  def fileAdded(file: OpenedFile) {
    log.info("{}: {}", file.info.path, file.info.mimeType)
    if (file.info.mimeType == Some("text/x-isabelle")) {
      val model = context.actorOf(Props(classOf[IsabelleDocumentModel], this.peer, project, session), "file" + file.info.id)
      registerDocumentModel(file.info.id, model)
    }
  }
  
  def fileChanged(file: OpenedFile, change: Operation, after: OpenedFile) = {
    
  }
  
  def fileClosed(file: OpenedFile) = {
    
  }
  
  def shutdown() {
    session.stop()    
  }
}