package clide.ghc

import akka.actor.ActorRef
import akka.actor.actorRef2Scala
import clide.assistants.DocumentModel
import clide.collaboration.Annotations
import clide.collaboration.Delete
import clide.collaboration.Insert
import clide.collaboration.Operation
import clide.collaboration.Retain
import clide.models.ProjectInfo
import scala.sys.process._
import java.io.InputStream
import java.io.ByteArrayInputStream
import java.io.File
import java.io.FileWriter
import java.io.InputStreamReader
import java.io.ByteArrayOutputStream
import java.io.PrintWriter

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
    List("errors" -> as)
  }    
  
  def changed(op: Operation) {
    log.info("change")
    self ! DocumentModel.Refresh
  }
    
  
  def initialize() {
    if (file.path.length > 1)
      new java.io.File(project.root + file.path.init.mkString("/")).mkdirs()      
    self ! DocumentModel.Refresh
  }
}