package clide.infrastructure

import akka.actor._
import scala.collection.mutable.Map
import scala.concurrent.duration._
import scala.util._
import clide.collaboration._

class HelloAnnotator(session: ActorRef) extends Actor with ActorLogging {
  val docs = Map[String,(Int,Document)]()
  
  var work: Option[Cancellable] = None
  
  private object Annotate
  
  def receive = {
    case HelloAnnotator.ListenTo(path) =>
      session ! SessionActor.OpenFile(path)
    case SessionActor.Initialize(path, revision, content) =>
      docs(path) = (revision,Document(content))
    case SessionActor.Edited(path, op) =>      
      val (rev,doc) = docs(path)
      doc(op) match {
        case Success(n) => docs(path) = (rev+1,n)
        case Failure(e) => throw e
      }
      import context.dispatcher
      if (work.isEmpty) work = Some(context.system.scheduler.scheduleOnce(100 millisecond){
        context.self ! Annotate
        work = None
      })
    case Annotate =>
      log.info("annotator run")
      docs.foreach { case (path,(rev,doc)) =>
        def parse(what: String): List[Annotation] = {
          what.toUpperCase().indexOf("HELLO") match {
	        case -1 => Plain(what.length)::Nil
	        case 0  => clide.collaboration.Annotate(5,scala.collection.immutable.Map("class" -> "keyword"))::parse(what.drop(5))
	        case n  => Plain(n)::clide.collaboration.Annotate(5,scala.collection.immutable.Map("class" -> "keyword"))::parse(what.drop(n+5))
	      }          
        }        
        session ! SessionActor.AnnotateFile(path,rev,AnnotationStream(parse(doc.content)))
      }
  }
}

object HelloAnnotator {
  case class ListenTo(path: String)
}