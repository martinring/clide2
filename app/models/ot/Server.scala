package models.ot

import scala.reflect.ClassTag
import akka.actor.{Actor,ActorRef,Props}
import scala.util.{Try,Success,Failure}

class Server(initialState: Document) extends Actor {
  var revision: Int = 0  
  var history: List[Operation] = Nil
  var state: Document = initialState
  var clients: Map[String,ActorRef] = Map.empty
  def receive = {
    case Register(name) =>
      clients += name -> sender
      sender ! Initialize(revision,state)
    case Change(rev, op) =>
      val res = for {
	    concurrentOps <- Try{ require(revision >= rev,"unknown revision"); history.take(revision - rev).reverse }
	    newOp <- concurrentOps.foldRight(Success(op): Try[Operation]) {
	      case (a,b) => b.flatMap(b => Operation.transform(a,b).map(_._1)) }
		newState <- state.apply(newOp)
	  } yield (newOp,newState)
	  res match {
	    case Success((newOp,newState)) => 
	      state = newState
	      revision += 1
	      history ::= newOp
	      clients.values.filter(_ != sender).foreach(_ ! Change(revision,newOp))
	      sender ! Acknowledgement
	    case Failure(e) =>
	      sender ! e
	  }
  }
}

object Server {
  def props(initialState: Document): Props = 
    Props(() => new Server(initialState))
}