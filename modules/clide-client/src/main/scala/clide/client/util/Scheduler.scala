package clide.client.util

import scalajs.js
import org.scalajs.dom._
import scala.concurrent.duration.Duration

object Scheduler {
  def scheduleOnce(delay: Duration)(task: => Unit): Cancellable = {
    val t = setTimeout(() => task, delay.length)
    Cancellable(clearTimeout(t))
  }
  
  def schedule(interval: Duration)(task: => Unit): Cancellable = {
    val i = setTimeout(() => task, interval.length)
    Cancellable(clearInterval(i))
  }
  
  def schedule(initialDelay: Duration, interval: Duration)(task: => Unit): Cancellable = {
    var i: Cancellable = null
    val t = scheduleOnce(initialDelay){
      i = schedule(interval)(task)
    }
    Cancellable{
      t.cancel()
      if (i != null) i.cancel()
    }
  }
}