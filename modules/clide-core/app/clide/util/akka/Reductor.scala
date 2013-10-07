package clide.util.akka

import akka.actor._
import scala.concurrent.duration._
import scala.reflect.ClassTag

/**
 * This actor can be used to reduce the number of updates sent to another actor
 * in high load situations.
 * An update will always be performed instantly except for updates, that come 
 * within a configured time span after another update. These updates get combined
 * until the time span elapsed. The cumulated update will then be sent to the
 * recipient
 */
class Reductor(
    recipient: ActorRef,
    combine: Option[Any] => Any => Option[Any],
    transform: Any => Any = identity) extends Actor {
  
  var combineDeadline = 0 seconds fromNow  
  var messageDeadline = 0 seconds fromNow
  
  var message: Option[Any] = None
  
  var tick: Option[Cancellable] = None
  
  private object Timeout
  
  def receive = {
    case t if messageDeadline.isOverdue || combineDeadline.isOverdue =>
      combine(message)(t).map(transform).foreach(recipient.forward)      
      combineDeadline = 500 milliseconds fromNow
      messageDeadline = 5   seconds      fromNow
      message         = None
    case t =>
      message = combine(message)(t)
      combineDeadline = 500 milliseconds fromNow
      
  }    
}