package clide.reactive.ui

import clide.reactive._
import scala.concurrent.duration._
import org.scalajs.dom

object Scheduler extends Scheduler {
  def now = (new scalajs.js.Date).valueOf().toLong
    
  def schedule[A](duration: FiniteDuration)(task: => A) = {      
    val interval = dom.setInterval(() => task, duration.toMillis)
    Ticket(dom.clearInterval(interval))
  }
   
  def scheduleOnce[A](duration: FiniteDuration)(task: => A) = {
    val timeout = dom.setTimeout(() => task, duration.toMillis)
    Ticket(dom.clearTimeout(timeout))
  }  
}