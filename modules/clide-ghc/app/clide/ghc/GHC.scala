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
import clide.collaboration.Annotations
import akka.actor.Actor
import clide.collaboration.AnnotationType
import clide.collaboration.Insert
import clide.collaboration.Delete

object GHC extends AssistantServer(GHCBehavior)

case class GHCBehavior(control: AssistantControl) extends AssistantBehavior {
  val mimeTypes = Set("text/x-haskell")  
  
  val log = control.log
  var project: ProjectInfo = null
  val cursorInfos: Map[Long,Map[Long,Annotations]] = Map.empty
  
  def start(project: ProjectInfo) {
    new java.io.File(project.root).mkdirs()
    this.project = project
    control.chat("i'm ready to go!")    
  }
  
  def stop {
    log.info("ghc stopped")    
  }    
  
  def fileOpened(file: OpenedFile) {
    
  }
  
  def fileActivated(file: OpenedFile) {   
    fileChanged(file,new Operation(List(Insert(file.state))),Seq.empty)
  }
  
  def fileInactivated(file: OpenedFile) {
    
  }
  
  def fileClosed(file: OpenedFile) {
    control.chat("closed " + file.toString)
    fileChanged(file,new Operation(List(Delete(file.state.length))),Seq.empty)
  }
  
  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) {    
    control.annotate(file, "substitutions", HaskellMarkup.substitutions(file.state))
	    
    val temp = new java.io.File(project.root + "/" + file.info.path.mkString("/"))
	val name = temp.getPath()
	
	val write = new FileWriter(temp)
	write.write(file.state)
	write.close()
		
	val lines = Seq("ghc-mod","check",name).lines ++ Seq("ghc-mod", "lint", name).lines
	val errs = lines.filter(_.startsWith(name)).map(_.drop(name.length() + 1)).map(HaskellMarkup.parseLine)
    val as = HaskellMarkup.toAnnotations(errs.toList.collect{ case Some(n) => n }, file.state)        
    
    control.annotate(file, "linting", as)
    
    cursors.foreach(cursorMoved)
  }
  
  def collaboratorJoined(who: SessionInfo){
    
  }
  
  def collaboratorLeft(who: SessionInfo){    
    cursorInfos.values.foreach(_.remove(who.id))
  }
  
  def cursorMoved(cursor: Cursor){
    val temp = new java.io.File(project.root + "/" + cursor.file.info.path.mkString("/"))
    val name = temp.getPath()
	
    val before = cursor.file.state.take(cursor.position)
    val line = before.count(_ == '\n') + 1
    val col  = before.length - before.lastIndexOf('\n')	
	
    val proc: Seq[String] = Seq("ghc-mod", "type", name, cursor.file.info.path.last.dropRight(3).capitalize, line.toString, col.toString)
    val lines = proc.lines
        
    val Line = "([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) \"(.*)\"".r
  
    val as = lines.headOption.getOrElse("") match { 
      case Line(fl,fc,tl,tc,msg) =>      
        val lengths = cursor.file.state.split("\n").map(_.length + 1)
	    val from = lengths.take(fl.toInt - 1).sum + fc.toInt - 1
	    val to   = lengths.take(tl.toInt - 1).sum + tc.toInt - 1  
	    new Annotations().plain(from).annotate(to-from, 
	      Set(AnnotationType.InfoMessage -> HaskellMarkup.prettify(msg),AnnotationType.Class -> "info")).plain(cursor.file.state.length - to)
      case _ =>
 	    new Annotations().plain(cursor.file.state.length)
    }
    
    val cursors = cursorInfos.get(cursor.file.info.id).getOrElse {
      cursorInfos(cursor.file.info.id) = Map.empty
      cursorInfos(cursor.file.info.id)
    }
            
    if (!cursors.isDefinedAt(cursor.owner.id) || cursors(cursor.owner.id) != as) {
      cursors(cursor.owner.id) = as            
      
      control.annotate(cursor.file, "cursor-info", cursors.values.reduce[Annotations]{
        case (a,b) => a.compose(b).get
      })
    }    
  }
}

object GHCApp extends App {
  GHC.startup()
  readLine()
  GHC.shutdown()
}