package clide.plugins

import clide.models._
import clide.collaboration._
import akka.actor.Props

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._      
     
  var session: Session = null    
  
  def startup() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty) {
      // TODO
    })
    session.phase_changed += { p => p match {
      case Session.Startup  => chat("I'm starting up, please wait a second!")
      case Session.Shutdown => chat("I'm shutting down")
      case Session.Inactive => // TODO: Set inactive
      case Session.Failed   => chat("Sorry, something failed")
      case Session.Ready    => chat("I'm ready to go!")
                               self ! AssistantSession.Activate
    } }
    session.syslog_messages += { msg => chat(XML.content(msg.body)) }
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