 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors.util

import akka.actor._
import scala.concurrent.duration._

/**
 * This actor can be used to reduce the number of updates sent to another actor
 * in high load situations.
 * An update will always be performed instantly except for updates, that come 
 * within a configured time span after another update. These updates get combined
 * until the time span elapsed. The cumulated update will then be sent to the
 * recipient. The default for the combine function is to take the newer update.
 * 
 * @author Martin Ring <martin.ring@dfki.de>
 */
class Reductor(
    recipient: ActorRef,
    combine: Option[Any] => Any => Option[Any] = (_ => Some.apply)) extends Actor {
  
  var combineDeadline = 0 seconds fromNow  
  var messageDeadline = 0 seconds fromNow
  
  var message: Option[Any] = None
  
  var tick: Option[Cancellable] = None
  
  private object Timeout
  
  def receive = {
    case t if messageDeadline.isOverdue || combineDeadline.isOverdue =>
      combine(message)(t).foreach(recipient.forward)
      combineDeadline = 500 milliseconds fromNow
      messageDeadline = 5   seconds      fromNow
      message         = None
    case t =>
      message = combine(message)(t)
      combineDeadline = 500 milliseconds fromNow
  }    
}