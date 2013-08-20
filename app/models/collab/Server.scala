package models.collab

import scala.reflect.ClassTag
import akka.actor.{Actor,ActorRef,Props}
import scala.util.{Try,Success,Failure}

class Server(initialState: Document) extends Actor {
  var revision: Int = 0  
  var history: List[Operation] = Nil
  var state: Document = initialState
  var clients: Map[String,ActorRef] = Map.empty
  def receive = {
    case Server.Register(name) =>
      println("registering "+name)
      clients += name -> sender
      println("answering")
      sender ! Server.Initialize(revision,state)
    case Server.Change(rev, op) =>
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
	      clients.values.filter(_ != sender).foreach(_ ! Server.Change(revision,newOp))
	      sender ! Server.Acknowledgement
	    case Failure(e) =>
	      sender ! e
	  }
  }
}

object Server {
  def props(initialState: Document): Props = 
    Props(() => new Server(initialState))
    
  trait Request
  case class Register(name: String) extends Request
  case class Initialize(revision: Int, document: Document) extends Request
  case class Change(revision: Int, operation: Operation) extends Request
  case class Error(message: String) extends Request
	
  trait Reply  
  case object Acknowledgement extends Reply
}