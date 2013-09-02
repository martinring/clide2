package models.collab

import scala.reflect.ClassTag
import akka.actor.{Actor,ActorRef,Props}
import scala.util.{Try,Success,Failure}
import play.Logger
import akka.actor.ActorLogging
import scala.collection.mutable.Buffer

class Server(initialState: Document) extends Actor with ActorLogging {   
  val history: Buffer[Operation] = Buffer.empty
  var state: Document = initialState
  var clients: List[ActorRef] = Nil
  
  def receive = {
    case Server.Register(name) => 
      log.info(f"client '$name' requested registration")      
      clients ::= sender
      sender ! Server.Initialize(history.length,state)
      Logger.info(f"client '$name' is successfully registerd")
      
    case Server.Edit(rev, op) =>
      val res = for {
	    concurrentOps <- Try{
	      require(rev >= 0, "negative revision number")
	      require(history.length >= rev, "invalid revision")
	      history.view(rev, history.length) 
	    }
	    op <- concurrentOps.foldLeft(Success(op): Try[Operation]) {
	      case (a,b) => a.flatMap(a => Operation.transform(a,b).map(_._1)) }
		state <- state.apply(op)
	  } yield (op,state)
	  res match {
	    case Success((op,nstate)) => 
	      state = nstate
	      history += op
	      clients.filter(_ != sender).foreach(_ ! Server.Edited(op))
	      sender ! Server.Acknowledgement
	    case Failure(e) =>
	      sender ! Server.Error(e.getMessage())
	  }
  }
  
  override def preStart() {
    log.info("ot server for started")
  }
  
  override def postStop() {
    log.info("ot server stopped")
  }  
}

object Server {
  def props(initialState: Document): Props = 
    Props(() => new Server(initialState))
    
  trait Request
  case class Register(name: String) extends Request  
  case class Edit(revision: Int, operation: Operation) extends Request  
	
  trait Reply  
  case class  Initialize(revision: Int, document: Document) extends Reply
  case class  Edited(operation: Operation) extends Reply
  case class  Error(message: String) extends Reply
  case object Acknowledgement extends Reply  
}