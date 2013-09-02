package models.collab

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
    
  def applyOperation(rev: Int, operation: Operation): Try[Operation] = {
    val result = for {
	  concurrentOps <- Try{
	    require((0 to revision) contains rev, "invalid revision")	    
	    history.view(rev, history.length) 
	  }
	  operation <- concurrentOps.foldLeft(Success(operation): Try[Operation]) {
	    case (a,b) => a.flatMap(a => Operation.transform(a,b).map(_._1)) }
	  nextState <- state(operation)
	} yield (nextState, operation)
	result.map {
	  case (nextState,operation) =>
	    state = nextState
	    operation
	}
  }
}