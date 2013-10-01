package clide.plugins

import clide.models._
import clide.collaboration._

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._    
  
  var thys = Map[String, OpenedFile]()
  
  implicit class OpenedIsabelleFile(val underlying: OpenedFile) {
    def path     = underlying.info.path.mkString("/")
    
    def nodeName = Document.Node.Name(
      path, project.root,
      underlying.info.path.lastOption.getOrElse("<unknown>"))
      
    def nodeHeader = 
      Exn.capture {
        sessionThyLoad.check_thy_text(nodeName, underlying.state)
      } match {
        case Exn.Res(header) => header
        case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
      }
      
    def perspective = 
      Text.Perspective(List(Text.Range(0,Integer.MAX_VALUE)))
      
    def initEdits = {
      val name = nodeName
      List(session.header_edit(name, nodeHeader),
           name -> Document.Node.Clear(),
           name -> Document.Node.Edits(List(Text.Edit.insert(0,underlying.state))),
           name -> Document.Node.Perspective(perspective))
    }
  }
   
  val sessionThyLoad = new Thy_Load(base_syntax = Outer_Syntax.empty) {
    override def append(dir: String, source_path: Path): String = {
      val path = source_path.expand
      if (path.is_absolute) Isabelle_System.platform_path(path)
      else source_path.implode
    }
    
    override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
      thys.get(name.node) match {
        case None => super.with_thy_text(name, f) // TODO: No file system access!!!
        case Some(file) => 
          val text = file.state
          Symbol.decode_strict(text)
          f(text)
      }      
    }
  }
  
  var session: Session = null
  
  override def startup() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))
    session.phase_changed    += (context.self ! _)
    session.commands_changed += (context.self ! _)
    session.syslog_messages  += (context.self ! _)    
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
    session.thy_load.base_syntax.scan(file.state).foldLeft(Annotations()) {
      case (as,t) =>
        val l = t.source.length
        if      (t.is_comment)   as.annotate(l, Map("c"->"cm-comment"))
        else if (t.is_string)    as.annotate(l, Map("c"->"cm-string")) 
        else if (t.is_sym_ident && Symbol.decode(t.source) != t.source) as.annotate(l, Map("c"->"sym","s"->Symbol.decode(t.source)))
        else if (t.is_sym_ident) as.annotate(l,Map("c"->"sym"))
        else as.plain(l)
    }
  }
  
  def isabelleMessages: Receive = {
    case phase: Session.Phase =>
      log.info("phase: " + phase.toString)
    case change: Session.Commands_Changed =>
      log.info(change.toString)
  }
  
  override def receive = isabelleMessages orElse super.receive
  
  override def postStop() {
    session.stop()
  }
}