package clide.isabelle

import akka.actor.Props

import clide.assistants._
import clide.collaboration.Operation
import clide.models._

import isabelle._

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  var session: Session = null
  
  var thys = Map[Document.Node.Name,OpenedFile]()
  
  def startup() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty) {
      override def append(dir: String, source_path: Path): String = {
        val path = source_path.expand
        if (path.is_absolute) Isabelle_System.platform_path(path)
        else {
          log.info("append({}, {})", dir, source_path)
          (Path.explode(dir) + source_path).expand.implode
        }
      }
      override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
        thys.get(name).map(file => f(file.state)).getOrElse {
          log.info("with_thy_text({}, {}), name, f")
          f("")
        }
      }    
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