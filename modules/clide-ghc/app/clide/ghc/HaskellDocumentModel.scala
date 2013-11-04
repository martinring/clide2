package clide.ghc

import java.io.FileWriter

import scala.sys.process.stringSeqToProcess

import akka.actor.ActorRef
import akka.actor.actorRef2Scala
import clide.assistants.DocumentModel
import clide.collaboration.Annotations
import clide.collaboration.Operation
import clide.models.ProjectInfo

class HaskellDocumentModel(server: ActorRef, project: ProjectInfo) extends DocumentModel(server, project) {
  def annotate: List[(String,Annotations)] = {    
    val temp = new java.io.File(project.root + "/" + file.path.mkString("/"))
	val name = temp.getPath()
	val write = new FileWriter(temp)
	write.write(state)
	write.close()
	var current = None
	val lines = Seq("ghc-mod","check",name).lines ++ Seq("ghc-mod", "lint", name)
	val Error = """.*([0-9]+).*""".r	
	val errs = lines.filter(_.startsWith(name)).map(_.drop(name.length() + 1)).map(HaskellMarkup.parseLine)
    val as = HaskellMarkup.toAnnotations(errs.toList.collect{ case Some(n) => n }, state)
    log.info("annotating: {}", as)
    List("errors" -> as, "substitutions" -> HaskellMarkup.substitutions(state))
  }    
  
  def changed(op: Operation) {
    log.info("change")
    triggerRefresh
  }    
  
  def initialize() {
    if (file.path.length > 1)
      new java.io.File(project.root + "/" + file.path.init.mkString("/")).mkdirs()
    triggerRefresh
  }
}