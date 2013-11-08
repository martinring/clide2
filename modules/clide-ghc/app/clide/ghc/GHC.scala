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

object GHC extends AssistantServer(GHCBehavior)

case class GHCBehavior(control: AssistantControl) extends AssistantBehavior {
  val log = control.log
  
  var project: ProjectInfo = null
  val workers: Map[Long,Future[Unit]] = Map.empty  
  
  implicit val executionContext = GHC.system.dispatcher
  
  def annotateFile(file: OpenedFile): Future[Unit] = Future {
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
  
  def start(project: ProjectInfo) = {
    this.project = project
    control.chat("ghc is here")
    Future.successful(())
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
  
  def fileChanged(file: OpenedFile, delta: Operation) {
    control.annotate(file, "substitutions", HaskellMarkup.substitutions(file.state))
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

object GHCApp extends App {
  GHC.startup()
  readLine()
  GHC.shutdown()
}