package clide.collaboration

import scala.util.Success

case class Client(val rev: Long, pending: Option[Operation] = None, buffer: Option[Operation] = None) {
  def localEdit(operation: Operation): (Boolean, Client) = 
    (pending.isEmpty, Client(rev, pending orElse Some(operation), buffer.map(Operation.compose(_,operation).get)))
    
  def remoteEdit(operation: Operation): (Operation, Client) = { 
    val t1 = pending.map(Operation.transform(_, operation).get)
    val t2 = buffer.flatMap(buf => t1.map { case (a1,b1) => Operation.transform(buf, b1).get } )
    (t2.map(_._2) orElse t1.map(_._2) getOrElse operation, Client(rev + 1, t1.map(_._1), t2.map(_._1)))
  }
  
  def ack: (Option[Operation], Client) = 
    (buffer, Client(rev + 1, buffer, None))
}