package clide.isabelle

import com.typesafe.config.ConfigFactory
import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import isabelle.Isabelle_System
import scala.concurrent.duration._
import clide.assistants.AssistantBehavior
import clide.assistants.AssistantControl
import clide.assistants.AssistantServer
import clide.models.ProjectInfo
import scala.concurrent.Future
import clide.models.OpenedFile
import scala.collection.mutable.Map
import clide.collaboration.Operation
import clide.models.SessionInfo
import isabelle.Build
import isabelle.Session
import scala.concurrent.Promise
import scala.concurrent.Await
import isabelle.XML
import isabelle.Path
import isabelle.Document

object Isabelle extends AssistantServer(IsabelleAssistantBehavior) {
  override def startup() {
    Isabelle_System.init()
    super.startup()
  }
  
  override def shutdown() {
    scala.actors.Scheduler.shutdown()
    super.shutdown()       
  }
}

case class IsabelleAssistantBehavior(control: AssistantControl) extends AssistantBehavior {
  val log = control.log
  
  var project: ProjectInfo = null
  val workers: Map[Long,Future[Unit]] = Map.empty
  var session: Session = null
  var thys: Map[Document.Node.Name,OpenedFile] = Map.empty
  
  implicit val executionContext = Isabelle.system.dispatcher
  
  def annotateFile(file: OpenedFile): Future[Unit] = Future {

  }
  
  def start(project: ProjectInfo) = {
    val ops = isabelle.Options.init
    val initialized = Promise[Unit]()
    log.info("building session content")
    val content = Build.session_content(ops, false, Nil, "HOL")   
    session = new Session(new isabelle.Thy_Load(content.loaded_theories, content.syntax) {
      override def append(dir: String, source_path: Path): String = {
        log.info("thy_load.append({}, {})", dir, source_path)
        val path = source_path.expand
        if (path.is_absolute) Isabelle_System.platform_path(path)
        else {          
          (Path.explode(dir) + source_path).expand.implode
        }
      }
      override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
        log.info("thy_load.with_thy_text({},{})", name, f)
        thys.get(name).map(file => f(file.state)).getOrElse {          
          f("")
        }
      }
      override def text_edits(reparse_limit: Int, previous: Document.Version, edits: List[Document.Edit_Text]) = {        
        val result = super.text_edits(reparse_limit, previous, edits)
        log.info("text_edits = {}", result)
        result
      }      
    })    
    session.phase_changed += { p => p match {
      case Session.Startup  => 
        control.chat("I'm starting up, please wait a second!")
      case Session.Shutdown => 
        control.chat("I'm shutting down")
      case Session.Inactive => 
        control.stop()
      case Session.Failed   =>
        control.chat("I couldn't start")
        initialized.failure(sys.error("isabelle session failed to initialize"))        
      case Session.Ready    =>         
        session.update_options(ops)
        initialized.success(())
        control.chat("I'm ready to go!")
        
    } }  
    session.syslog_messages += { msg => control.chat(XML.content(msg.body)) } 
    session.raw_output_messages += { msg =>
      log.info("OUTPUT: {}", XML.content(msg.body))
    }
    session.start(List("-S","HOL"))        
    this.project = project
    control.chat("ghc is here")
    // TODO: There should be a better solution than blocking
    initialized.future
  }
  
  def stop {
    session.stop()
  }
  
  def mimeTypes = Set("text/x-isabelle")
  
  def fileOpened(file: OpenedFile) {
    workers(file.info.id) = annotateFile(file)
    control.chat("opened " + file.toString)
  }
  
  def fileActivated(file: OpenedFile) {
    control.chat("activated " + file.toString)
  }
  
  def fileInactivated(file: OpenedFile) {
    control.chat("inactivated " + file.toString)
  }
  
  def fileClosed(file: OpenedFile) {
    control.chat("closed " + file.toString)
  }
  
  def fileChanged(file: OpenedFile, delta: Operation) {
    control.annotate(file, "substitutions", IsabelleMarkup.substitutions(file.state))
    control.chat("changed " + file.toString)
    if (workers.get(file.info.id).map(!_.isCompleted).getOrElse(false)) {
      
    } else {
      workers(file.info.id) = annotateFile(file)
    }
  }
  
  def collaboratorJoined(who: SessionInfo){
    control.chat("joined " + who)
  }
  
  def collaboratorLeft(who: SessionInfo){
    control.chat("left " + who)
  }
  
  def cursorMoved(file: OpenedFile, owner: SessionInfo, offset: Int){
    control.chat("cursor moved")
  }
}

object IsabelleApp extends App {
  Isabelle.startup()
  readLine()
  Isabelle.shutdown()  
}