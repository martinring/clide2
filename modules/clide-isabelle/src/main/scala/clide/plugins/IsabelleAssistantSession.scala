package clide.plugins

import clide.models._
import clide.collaboration._

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._    
  
  var thys = Map[String, OpenedFile]()
  
  implicit class OpenedIsabelleFile(val underlying: OpenedFile) {
    def path     = underlying.info.path.mkString("/")
    def nodeName = Document.Node.Name(
        underlying.info.path.mkString("/"),
        project.root,
        underlying.info.path.lastOption.getOrElse("<unknown>"))
  }
   
  val sessionThyLoad = new Thy_Load(base_syntax = Outer_Syntax.empty) {
    override def append(dir: String, source_path: Path): String = {
      val path = source_path.expand
      if (path.is_absolute) Isabelle_System.platform_path(path)
      else source_path.implode
    }
    
    override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
      thys.get(name.node) match {
        case None => super.with_thy_text(name, f)
        case Some(file) => // TODO: No file system access!!!
          val text = file.state
          Symbol.decode_strict(text)
          f(text)
      }      
    }
  }
  
  var session: Session = null
  
  override def startup() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))
    session.phase_changed += { phase =>
      log.info(s"phase: $phase")
    }
    session.commands_changed += { change =>
      log.info(s"commands changed")
    }
    session.start(List("HOL"))    
  }
  
  def fileAdded(file: OpenedFile) {
    log.info("{}: {}", file.path, file.info.mimeType)
    if (file.info.mimeType == "text/x-isabelle") {
      log.info(s"I am watching ${file.path}")
      thys += file.path -> file
    }
  }
  
  def fileChanged(file: OpenedFile, change: Operation, after: OpenedFile) = {
    log.info("change")
    processFile(after).map(annotate(after, _))
    thys.get(file.path).foreach { file =>
      val (_,edits) = change.actions.foldLeft((0,Nil : List[Text.Edit])) { 
        case ((i,edits),Retain(n)) =>
          (i+n,edits)
        case ((i,edits),Delete(n)) =>
          (i+n,Text.Edit.remove(i,Seq.fill(n)('-').mkString) :: edits)
        case ((i,edits),Insert(s)) =>
          (i+s.length,Text.Edit.insert(i,s) :: edits)
      }
      log.info(s"edits in file ${file.path}: $edits")
      session.update((file.nodeName, Document.Node.Edits[Text.Edit,Text.Perspective](edits)) :: Nil)
    }
  }
      
  
  def fileClosed(file: OpenedFile) {
    thys.get(file.path).map { file =>
      thys -= file.path
    }
  }  
  
  def processFile(file: OpenedFile) = Some {
    Annotations(session.thy_load.base_syntax.scan(file.state).map { case t: isabelle.Token =>
        (if (t.is_command) {
          Annotate(t.source.length(),Map("c"->"cm-keyword"))	       
	    } else if (t.is_comment) {
	      Annotate(t.source.length(),Map("c"->"cm-comment"))
	    } else if (t.is_begin) {
	      Annotate(t.source.length(),Map("c"->"cm-keyword"))
	    } else if (t.is_end) {
	      Annotate(t.source.length(),Map("c"->"cm-keyword"))
	    } else if (t.is_keyword) {
	      Annotate(t.source.length(),Map("c"->"cm-keyword"))
	    } else if (t.is_text) {
	      Annotate(t.content.length(),Map("c"->"cm-quote"))
	    } else if (t.is_comment) {
	      Annotate(t.content.length(),Map("c"->"cm-comment"))	      
	    } else if (t.is_string) {
	      Annotate(t.content.length(),Map("c"->"cm-string"))          
        } else Plain(t.content.length()))
      })    
  }
  
  override def postStop() {
    session.stop()
  }
}