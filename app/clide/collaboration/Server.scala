package clide.collaboration

import scala.reflect.ClassTag
import akka.actor.{Actor,ActorRef,Props}
import scala.util.{Try,Success,Failure}
import play.Logger
import akka.actor.ActorLogging
import scala.collection.mutable.Buffer

class Server(initialState: Document) {
  private val history: Buffer[Operation] = Buffer.empty
  private var state: Document = initialState  
  
  def text = state.content
  def revision = history.length
  def getHistory = history.view
    
  def applyOperation(operation: Operation, rev: Long): Try[Operation] = {
    val result = for {
	  concurrentOps <- Try {
	    require((0 to revision) contains rev, "invalid revision: " + rev)	    
	    history.view(rev.toInt, revision) // TODO: Long Revisions 
	  }
	  operation <- concurrentOps.foldLeft(Success(operation): Try[Operation]) {
	    case (a,b) => a.flatMap(a => Operation.transform(a,b).map(_._1)) }
	  nextState <- state(operation)
	} yield (nextState, operation)
	result.map {
	  case (nextState,operation) =>
	    history.append(operation)
	    state = nextState	    
	    operation
	}
  }
  
  def transformAnnotation(rev: Int, as: AnnotationStream): Try[AnnotationStream] = for {
      concurrentOps <- Try {
        require((0 to revision) contains rev, "invalid revision: " + rev)
        history.view(rev, revision)
      }
      annotation <- concurrentOps.foldLeft(Success(as): Try[AnnotationStream]) {
        case (a,b) => a.flatMap(a => AnnotationStream.transform(a,b)) }      
  } yield annotation    
}