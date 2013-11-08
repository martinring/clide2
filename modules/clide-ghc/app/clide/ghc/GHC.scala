package clide.ghc

import com.typesafe.config.ConfigFactory
import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import scala.concurrent.duration._
import clide.assistants.{AssistantServer, AssistantBehavior, AssistantControl}
import clide.models._
import clide.collaboration.Operation
import akka.actor.ActorLogging
import akka.actor.Cancellable
import scala.collection.mutable.Map
import scala.concurrent.Future
import scala.sys.process._
import java.io.FileWriter
import clide.assistants.Cursor

object GHC extends AssistantServer(GHCBehavior)

case class GHCBehavior(control: AssistantControl) extends AssistantBehavior {
  val log = control.log
  
  var project: ProjectInfo = null
  val workers: Map[Long,Future[Unit]] = Map.empty
  
  implicit val executionContext = GHC.system.dispatcher
  
  def supplyCursorInfo(cursor: Cursor): Future[Unit] = Future {
    try {
    val temp = new java.io.File(project.root + "/" + cursor.file.info.path.mkString("/"))
	val name = temp.getPath()
	
	val before = cursor.file.state.take(cursor.position)
	val line = before.count(_ == '\n') + 1
	val col  = before.length - before.lastIndexOf('\n') - 1	
	
    val lines = Seq("ghc-mod","type", name, cursor.file.info.path.last.dropRight(3).capitalize, line.toString, col.toString).lines
    control.chat(lines.mkString("\n"))
    }
    catch {
      case e: Throwable => log.info("e: {}", e)
    }
  }
  
  def annotateFile(file: OpenedFile, cursors: Seq[Int] = Seq.empty): Future[Unit] = Future {
    control.annotate(file, "substitutions", HaskellMarkup.substitutions(file.state))
    
    val temp = new java.io.File(project.root + "/" + file.info.path.mkString("/"))
	val name = temp.getPath()
	
	val write = new FileWriter(temp)
	write.write(file.state)
	write.close()
		
	val lines = Seq("ghc-mod","check",name).lines ++ Seq("ghc-mod", "lint", name)
	val errs = lines.filter(_.startsWith(name)).map(_.drop(name.length() + 1)).map(HaskellMarkup.parseLine)
    val as = HaskellMarkup.toAnnotations(errs.toList.collect{ case Some(n) => n }, file.state)        
    
    control.annotate(file, name, as)    
  }
  
  def start(project: ProjectInfo) = Future {
    new java.io.File(project.root).mkdirs()
    this.project = project
    control.chat("ghc is here")
  }
  
  def stop {
    log.info("ghc stopped")
    control.chat("ghc is leaving")
  }
  
  val mimeTypes = Set("text/x-haskell")
  
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
  
  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) {    
    if (workers.get(file.info.id).map(_.isCompleted) getOrElse true) {
      workers(file.info.id) = annotateFile(file)
    } else {
      log.info("waiting for worker to complete")      
    }
  }
  
  def collaboratorJoined(who: SessionInfo){
    control.chat("joined " + who)
  }
  
  def collaboratorLeft(who: SessionInfo){
    control.chat("left " + who)
  }
  
  def cursorMoved(cursor: Cursor){
    if (workers.get(cursor.file.info.id).map(_.isCompleted) getOrElse true) {
      workers(cursor.file.info.id) = supplyCursorInfo(cursor)
    } else {
      log.info("waiting for worker to complete")
    }
  }
}

object GHCApp extends App {
  GHC.startup()
  readLine()
  GHC.shutdown()
}