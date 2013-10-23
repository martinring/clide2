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
  private var headRev: Long = 0
  private var rev: Long     = 0  
  private var doc: Document = Document("")
  private var pending: Option[Operation] = None
  private val annotations = Map[String,Option[Annotations]]()
  
  var flushTimeout: Option[Cancellable] = None
  var flushMaxTimeout: Option[Cancellable] = None
  var refreshTimeout: Option[Cancellable] = None
  var needRefresh = false
  
  def revision = rev
  def state    = doc.content
  def file     = info
  
  def initialize()  
  def changed(op: Operation)
  def annotate: List[(String,Annotations)]    
     
  private def flush() = {
    pending.foreach { op =>
      rev = headRev
      doc = doc(op).get      
      pending = None
      changed(op)
    }
  }
  
  private object RefreshTimeout
      
  def initialized: Receive = {
    import context.dispatcher
    
    {
      case Change(change) =>
        headRev += 1
		pending = Some(pending.fold(change)(a => Operation.compose(a, change).get))
		flushTimeout.foreach(_.cancel)		
		flushTimeout = Some {  // TODO: Move timing to config
		  context.system.scheduler.scheduleOnce(500 milliseconds, self, Flush)
		}
		if (!flushMaxTimeout.isDefined) flushMaxTimeout = Some {
		  context.system.scheduler.scheduleOnce(2 seconds, self, Flush)
		}
		  
      case Flush =>
        flushMaxTimeout.map(_.cancel)
	    flushTimeout.map(_.cancel)
	    flushMaxTimeout = None    
	    flushTimeout = None
        flush()
		
      case RefreshTimeout =>
        refreshTimeout = None
        if (needRefresh) {
          needRefresh = false
          self ! Refresh
        }
        
	  case Refresh =>
	    if (refreshTimeout.isEmpty) {
	      annotate.foreach { case (name, annotations) =>
			log.info("annotation: {}, state: {}", annotations.length, state.length)
			server ! clide.actors.Messages.Annotate(info.id, revision, annotations, name)			 
		  }
		  refreshTimeout = Some{ // TODO: Move timing to config
		    context.system.scheduler.scheduleOnce(1 second, self, RefreshTimeout)
		  }
	    } else {
	      needRefresh = true
	    }	    
    }
  }
  
  def receive = {
    case Init(init) =>
      rev  = init.revision
      headRev = rev
      doc  = Document(init.state)
      info = init.info
      initialize()
      context.become(initialized)
  }
}