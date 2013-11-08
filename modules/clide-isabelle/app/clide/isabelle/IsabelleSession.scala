package clide.isabelle

import clide.assistants.AssistantBehavior
import clide.models._
import scala.concurrent.Promise
import isabelle.Session
import isabelle.Build
import isabelle.Path
import isabelle.Document
import isabelle.XML
import isabelle.Isabelle_System

trait IsabelleSession { self: AssistantBehavior with Control =>
  var session: Session = null
  var project: ProjectInfo = null
  
  def start(project: ProjectInfo) = {
    this.project = project
    val ops = isabelle.Options.init
    val initialized = Promise[Unit]()
    control.log.info("building session content")
    val content = Build.session_content(ops, false, Nil, "HOL")   
    session = new Session(new isabelle.Thy_Load(content.loaded_theories, content.syntax) {
      override def append(dir: String, source_path: Path): String = {
        control.log.info("thy_load.append({}, {})", dir, source_path)
        val path = source_path.expand
        if (path.is_absolute) Isabelle_System.platform_path(path)
        else {          
          (Path.explode(dir) + source_path).expand.implode
        }
      }
      override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
        control.log.info("thy_load.with_thy_text({},{})", name, f)
        //thys.get(name).map(file => f(file.state)).getOrElse {          
          f("")
        //}
      }
      override def text_edits(reparse_limit: Int, previous: Document.Version, edits: List[Document.Edit_Text]) = {        
        val result = super.text_edits(reparse_limit, previous, edits)
        control.log.info("text_edits = {}", result)
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
    session.syslog_messages += { msg => 
      control.log.info("SYSLOG: {}", XML.content(msg.body))
      control.chat(XML.content(msg.body)) 
    } 
    session.raw_output_messages += { msg =>
      control.log.info("OUTPUT: {}", XML.content(msg.body))
    }
    session.start(List("-S","HOL"))            
    control.chat("ghc is here")
    // TODO: There should be a better solution than blocking
    initialized.future
  }
  
  def stop {
    session.stop()
  }
}