package clide.client.util

import scalajs.js
import org.scalajs.dom._

object Scheduler {
  def scheduleOnce(delay: Long)(task: => Unit): Cancellable = {
    val t = setTimeout(() => task, delay)
    Cancellable(clearTimeout(t))
  }
  
  def schedule(interval: Long)(task: => Unit): Cancellable = {
    val i = setTimeout(() => task, interval)
    Cancellable(clearInterval(i))
  }
  
  def schedule(initialDelay: Long, interval: Long)(task: => Unit): Cancellable = {
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