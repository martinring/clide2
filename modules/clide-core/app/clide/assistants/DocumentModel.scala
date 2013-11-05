 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.assistants

import clide.models._
import clide.collaboration._
import akka.actor._
import scala.collection.mutable.{Buffer,Map}
import scala.concurrent.Promise
import scala.concurrent.duration._
import clide.actors.Messages._
import scala.xml.XML

object DocumentModel {
  case object Close
  case class  Change(op: Operation)
  case class  Init(f: OpenedFile)
  case class  RequestInfo(offset: Int, user: SessionInfo)
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
  
  private var flushTimeout: Option[Cancellable] = None
  private var flushMaxTimeout: Option[Cancellable] = None
  private var refreshTimeout: Option[Cancellable] = None
  private var needRefresh = false
  
  def revision = rev
  def state    = doc.content
  def file     = info
  
  def chat(msg: String) = server ! Talk(None,msg)
  
  def initialize()
  def changed(op: Operation)
  def annotate: List[(String,Annotations)]
  
  def getInfo(pos: Int): Option[String]

  def triggerRefresh() = context.self ! Refresh
  def triggerClose()   = context.self ! Close
     
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
    initialize()
    
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
		
      case RequestInfo(pos, user) =>        
        getInfo(pos).foreach{ m =>
          chat("@" + user.user + ": " + m)
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
	  
	  case Close =>
	    context.stop(self)
    }
  }
  
  def receive = {
    case Init(init) =>
      rev  = init.revision
      headRev = rev
      doc  = Document(init.state)
      info = init.info      
      context.become(initialized)
  }
}