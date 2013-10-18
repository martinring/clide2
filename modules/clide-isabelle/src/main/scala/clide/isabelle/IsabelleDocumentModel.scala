package clide.isabelle

import akka.actor.ActorRef
import akka.actor.actorRef2Scala
import clide.assistants.DocumentModel
import clide.collaboration.Annotations
import clide.collaboration.Delete
import clide.collaboration.Insert
import clide.collaboration.Operation
import clide.collaboration.Retain
import clide.models.ProjectInfo
import isabelle.Document
import isabelle.Exn
import isabelle.Session
import isabelle.Text
import isabelle.Thy_Header

class IsabelleDocumentModel(server: ActorRef, project: ProjectInfo, session: Session) extends DocumentModel(server, project) {  
  def nodeName = {
    val name = file.path.mkString("/")
    Thy_Header.thy_name(name).map { theory =>
      Document.Node.Name(name, project.root, theory)
    }
  }.get
  
  def nodeHeader = 
    Exn.capture {      
      session.thy_load.check_thy_text(nodeName, state)
    } match {
      case Exn.Res(header) => header
      case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
    }
 
  var overlays = Document.Node.Overlays.empty
  
  def insertOverlay(command: isabelle.Command, fn: String, args: List[String]) = {
    overlays = overlays.insert(command, fn, args)
  }
  
  def removeOverlay(command: isabelle.Command, fn: String, args: List[String]) = {
    overlays = overlays.remove(command, fn, args)
  }
       
  def perspective: Document.Node.Perspective_Text = {
    Document.Node.Perspective(true, Text.Perspective.full, overlays)
  }
    
  def initEdits: List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])] = {
    val name = nodeName
    List(session.header_edit(name, nodeHeader),
         name -> Document.Node.Clear(),
         name -> Document.Node.Edits(List(Text.Edit.insert(0,state))),
         name -> perspective)
  }
  
  def opToEdits(operation: Operation): List[Document.Edit_Text] = {    
    val name = nodeName
    val (_,edits) = operation.actions.foldLeft((0,Nil : List[Text.Edit])) { 
      case ((i,edits),Retain(n)) => (i+n,edits)
      case ((i,edits),Delete(n)) => (i+n,Text.Edit.remove(i,Seq.fill(n)('-').mkString) :: edits)
      case ((i,edits),Insert(s)) => (i+s.length,Text.Edit.insert(i,s) :: edits)
    }
    List(session.header_edit(name, nodeHeader),
      name -> Document.Node.Edits(edits.reverse), // TODO: reverse needed??
      name -> perspective)
  }
  
  def annotate: List[(String,Annotations)] = {
    List("highlighting"  -> IsabelleMarkup.highlighting(nodeHeader,session.snapshot(nodeName,Nil)),
         "substitutions" -> IsabelleMarkup.substitutions(state))
  }
    
  
  def changed(op: Operation) {
    val edits = opToEdits(op)
    log.info("sending edits: {}", edits)
    session.update(edits)    
    self ! DocumentModel.Refresh
  }
  
  def initialize() {
    log.info("name: {}, header: {}", nodeName, nodeHeader)
    session.update(initEdits)
    session.commands_changed += { change =>
      log.info("commands changed: {}", change)
      self ! DocumentModel.Refresh
    }
  }
}