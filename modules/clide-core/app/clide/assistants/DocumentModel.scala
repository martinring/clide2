package clide.assistants

import clide.models._
import clide.collaboration._
import akka.actor._
import scala.collection.mutable.{Buffer,Map}
import scala.concurrent.Promise
import scala.concurrent.duration._
import clide.actors.Messages

object DocumentModel {
  case object Close
  case class  Change(op: Operation)
  case class  Init(f: OpenedFile)
  case object Refresh
  case object Flush
}

abstract class DocumentModel(server: ActorRef, val project: ProjectInfo) extends Actor with ActorLogging {
  import DocumentModel._ 
  
  private var info: FileInfo = null
  private var rev: Long     = 0
  private var doc: Document = Document("")
  private var pending: Option[Operation] = None
  private val annotations = Map[String,Option[Annotations]]()
  
  var flushTimeout: Option[Cancellable] = None
  
  def revision = rev
  def state    = doc.content
  def file     = info
  
  def initialize()  
  def changed(op: Operation)
  def annotate: List[(String,Annotations)]    
     
  private def flush() = {
    pending.foreach { op =>
      changed(op)
      pending = None
    }
  }
      
  def initialized: Receive = {
    import context.dispatcher
    
    {
      case Change(change) =>
		pending = Some(pending.fold(change)(a => Operation.compose(a, change).get))
		flushTimeout.foreach(_.cancel)
		flushTimeout = Some {
		  context.system.scheduler.scheduleOnce(700 milliseconds, self, Flush)
		}
		  
      case Flush =>
        flush()
		
	  case Refresh =>
		annotate.foreach { case (name, annotations) =>
		  server ! clide.actors.Messages.Annotate(info.id, revision, annotations, name)
		}
    }
  }
  
  def receive = {
    case Init(init) =>
      rev  = init.revision
      doc  = Document(init.state)
      info = init.info
      initialize()
      context.become(initialized)
  }
}