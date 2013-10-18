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
  def runCommand(cmd: Seq[String]): (Int, String, String) = {
	val stdout = new ByteArrayOutputStream
	val stderr = new ByteArrayOutputStream
	val stdoutWriter = new PrintWriter(stdout)
	val stderrWriter = new PrintWriter(stderr)
	val exitValue = cmd.!(ProcessLogger(stdoutWriter.println, stderrWriter.println))
	stdoutWriter.close()
	stderrWriter.close()
	(exitValue, stdout.toString, stderr.toString)
  }
      
  def annotate: List[(String,Annotations)] = {
    val temp = File.createTempFile("ghc", ".hs")
	val name = temp.getAbsolutePath()
	val write = new FileWriter(temp)
	write.write(state)
	write.close()    
	var current = None
	val (ec,stdout,stderr) = runCommand(Seq("ghc",name))
	val Error = """.*([0-9]+).*""".r
	val errs = stderr.split(name.replace("\\", "\\\\")).filter(_.trim.length > 0).map { e =>	  
      HaskellMarkup.parse(HaskellMarkup.error, e) match {
        case HaskellMarkup.Success(((l,c),o),_) => Some(((l,c),o))
        case HaskellMarkup.Failure(_,_) => None
        case HaskellMarkup.Error(_,_) => None
      }
    }
    val as = HaskellMarkup.toAnnotations(errs.toList.collect{ case Some(n) => n }, state)
    log.info("annotating: {}", as)
    List("errors" -> as)
  }    
  
  def changed(op: Operation) {
    log.info("change")
    self ! DocumentModel.Refresh
  }
    
  
  def initialize() {
    self ! DocumentModel.Refresh
  }
}