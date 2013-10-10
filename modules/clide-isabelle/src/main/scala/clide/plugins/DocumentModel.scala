package clide.plugins

import clide.models._
import clide.collaboration._
import akka.actor._
import scala.collection.mutable.Buffer
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
  private val pending = Buffer.empty[Operation]  
  
  def revision = rev
  def state    = doc.content
  def file     = info
  
  def initialize()  
  def changed(op: Operation)
  def annotate: Annotations
     
  private def flush() = {
    var result: Option[Operation] = None
    pending.foreach { op =>
      rev   += 1
      doc    = doc(op).get
      result = Some{
        result.fold(op)(a => Operation.compose(a, op).get)
      }
    }
    pending.clear()
    result.map(changed(_))
  }
  
  def initialized: Receive = {
    case Change(change) =>
      pending += change
      
    case Flush =>
      flush()
    
    case Refresh =>
      server ! clide.actors.Messages.Annotate(info.id, revision, annotate)
  }
  
  def receive = {
    case Init(init) =>
      rev  = init.revision
      doc  = Document(init.state)
      info = init.info
      context.become(initialized)     
      context.system.scheduler.schedule(1 second, 2 seconds, self, Flush)(context.dispatcher, self)
      initialize()
  }
}