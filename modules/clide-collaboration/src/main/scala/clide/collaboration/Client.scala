package clide.collaboration

import scala.util.Success

abstract class Client(private var rev: Long = 0) {
  private trait State
  private object Synchronized extends State
  private case class Waiting(op: Operation) extends State
  private case class Buffering(op: Operation, buffer: Operation) extends State
  private var state: State = Synchronized
  private def nextRevision() = rev += 1

  def revision = rev

  /**
   * an operation occurs on the client side.
   * @return possibly an operation to send to the server
   */
  def applyClient(operation: Operation): Option[Operation] = {       
    state match {
      case Synchronized => // send operation and wait for acknowledgement        
        state = Waiting(operation)
        Some(operation)
      case Waiting(op) => // buffer operation
        state = Buffering(op,operation)
        None
      case Buffering(op,buffer) => // compose operation into buffer
        val newBuffer = Operation.compose(buffer,operation).get
        state = Buffering(op,newBuffer)
        None
    }
  }

  /**
   * an operation arrives from the server
   * @return the possibly transformed operation to apply on the client
   */
  def applyServer(operation: Operation): Operation = {
    nextRevision()
    state match {
      case Synchronized => // just apply the operation
        state = Synchronized
        operation        
      case Waiting(op) => // transform the outstanding operation a against the incoming b such that
                          // transform(a,b) = (a',b') and compose(a,b') == compose(b,a')
                          // apply the transformed server operation b' to client. 
                          // wait with transformed outstanding a'
        val Success((a,b)) = Operation.transform(op, operation)        
        state = Waiting(a)
        b
      case Buffering(op,buffer) => // transform the outstanding operation against the incoming as above
                                   // and also transform the buffer against the transformed server operation.
        val Success((a1,b1)) = Operation.transform(op, operation)
        val Success((a2,b2)) = Operation.transform(buffer, b1)
        state = Buffering(a1,a2)
        b2        
    }
  }
  
  /**
   * an acknowledgment for an operation arrives from the server
   * @return possibly a buffered operation to send back to the server
   */
  def acknowledgeEdit(): Option[Operation] = {
    nextRevision()
    state match {  
      case Synchronized =>
        sys.error("Unexpected Acknowledgement")
      case Waiting(op) =>
        state = Synchronized
        None
      case Buffering(op,buffer) =>        
        state = Waiting(buffer)
        Some(buffer)
    }
  }
}