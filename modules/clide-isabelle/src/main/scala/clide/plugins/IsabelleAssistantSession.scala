package clide.plugins

import clide.models._
import clide.collaboration._

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._    
  
  val thys = scala.collection.mutable.Map[Document.Node.Name, OpenedFile]()
  
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
      
    def initEdits: List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])] = {
      val name = nodeName
      List(session.header_edit(name, nodeHeader),
           name -> Document.Node.Clear(),
           name -> Document.Node.Edits(List(Text.Edit.insert(0,underlying.state))),
           name -> Document.Node.Perspective(perspective))
    }
    
    def opToEdits(operation: Operation): List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])] = {
      val (_,edits) = operation.actions.foldLeft((0,Nil : List[Text.Edit])) { 
        case ((i,edits),Retain(n)) =>
          (i+n,edits)
        case ((i,edits),Delete(n)) =>
          (i+n,Text.Edit.remove(i,Seq.fill(n)('-').mkString) :: edits)
        case ((i,edits),Insert(s)) =>
          (i+s.length,Text.Edit.insert(i,s) :: edits)
      }
      (nodeName, Document.Node.Edits[Text.Edit,Text.Perspective](edits)) :: Nil
    }
  }
   
  val sessionThyLoad = new Thy_Load(base_syntax = Outer_Syntax.empty) {
    override def append(dir: String, source_path: Path): String = {
      val path = source_path.expand
      if (path.is_absolute) Isabelle_System.platform_path(path)
      else source_path.implode
    }
    
    override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A = {
      thys.get(name) match {
        case None => super.with_thy_text(name, f) // TODO: No file system access!!!
        case Some(file) => 
          val text = file.state
          Symbol.decode_strict(text)
          f(text)
      }      
    }
  }
  
  var session: Session = null
  
  override def preStart() {
    session = new Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))
    session.phase_changed    += (context.self ! _)
    session.commands_changed += (context.self ! _)
    session.syslog_messages  += (context.self ! _)
    session.start(List("HOL"))
    super.preStart()
  }
  
  def fileAdded(file: OpenedFile) {
    log.info("{}: {}", file.path, file.info.mimeType)
    if (file.info.mimeType == Some("text/x-isabelle")) {
      log.info(s"I am watching ${file.path}")
      thys(file.nodeName) = file
    }
  }
  
  def fileChanged(file: OpenedFile, change: Operation, after: OpenedFile) = {
    thys(file.nodeName) = after    
    session.update(file.opToEdits(change))
  }
  
  def fileClosed(file: OpenedFile) = {
    // TODO: Unwatch
    thys.remove(file.nodeName)
  }
  
  def processFile(file: OpenedFile) = {    
    val snap = session.snapshot(file.nodeName, Nil)
    IsabelleMarkup.getTokens(snap, Text.Range(0,file.state.length)).foldLeft(new Annotations) { case (as,info) =>
      info.info match {
        case Nil => as.plain(info.range.length)
        case c   => as.annotate(info.range.length,Map("c"->c.mkString(" ")))
      }
    }
  }
  
  def receiveIsabelle: Receive = {
    case Session.Ready =>
      log.info("session is ready... initializing")
      session.update(thys.values.toList.flatMap(_.initEdits))
    case output: Isabelle_Process.Output =>
      log.info(output.message.toString)
    case change: Session.Commands_Changed =>
      change.nodes.foreach { node =>
        thys.get(node).map { file =>
          log.info("annotating " + file.nodeName)
          annotate(file, processFile(file))
        }
      }
  }
  
  override def receive = receiveIsabelle orElse super.receive
  
  override def postStop() {
    session.stop()
    super.postStop()
  }
}