package clide.isabelle

import com.typesafe.config.ConfigFactory
import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import isabelle.Isabelle_System
import scala.concurrent.duration._
import clide.assistants.AssistantBehavior
import clide.assistants.AssistantControl
import clide.assistants.AssistantServer
import clide.models.ProjectInfo
import scala.concurrent.Future
import clide.models.OpenedFile
import scala.collection.mutable.Map
import clide.collaboration.Operation
import clide.models.SessionInfo
import isabelle.Build
import isabelle.Session
import scala.concurrent.Promise
import scala.concurrent.Await
import isabelle.XML
import isabelle.Path
import isabelle.Document

object Isabelle extends AssistantServer(IsabelleAssistantBehavior) {
  override def startup() {
    Isabelle_System.init()
    super.startup()
  }
  
  override def shutdown() {
    scala.actors.Scheduler.shutdown()
    super.shutdown()       
  }
}

trait Control {
  def control: AssistantControl
}

case class IsabelleAssistantBehavior(control: AssistantControl) extends AssistantBehavior with Control 
  with IsabelleSession {  
  
  var project: ProjectInfo = null
  val workers: Map[Long,Future[Unit]] = Map.empty
  var session: Session = null
  var thys: Map[Document.Node.Name,OpenedFile] = Map.empty
  
  implicit val executionContext = Isabelle.system.dispatcher
  
  def annotateFile(file: OpenedFile): Future[Unit] = Future {

  }    
  
  def mimeTypes = Set("text/x-isabelle")
  
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
  
  def fileChanged(file: OpenedFile, cursors: List[(SessionInfo,Int)], delta: Operation) {
    control.annotate(file, "substitutions", IsabelleMarkup.substitutions(file.state))
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

object IsabelleApp extends App {
  Isabelle.startup()
  readLine()
  scala.actors.Scheduler.shutdown()
  Isabelle.shutdown()  
  Isabelle.system.awaitTermination()
  sys.exit()
}