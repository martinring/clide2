package clide.reactive

import org.scalajs.dom
import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.Promise
import scala.util.Try

trait Scheduler {
  def now: Long
  def schedule[A](duration: FiniteDuration)(task: => A): Cancellable
  def scheduleOnce[A](duration: FiniteDuration)(task: => A): Cancellable
  
  def timeout[A](duration: FiniteDuration): Future[Unit] = {
    val promise = Promise[Unit]
    schedule(duration)(promise.success(()))
    promise.future
  }
}

object Scheduler {
  implicit val jsScheduler = new Scheduler {
    def now = (new scalajs.js.Date).valueOf().toLong
    
    def schedule[A](duration: FiniteDuration)(task: => A) = {      
      val interval = dom.setInterval(() => task, duration.toMillis)
      Cancellable(dom.clearInterval(interval))
    }
    
    def scheduleOnce[A](duration: FiniteDuration)(task: => A) = {
      val timeout = dom.setTimeout(() => task, duration.toMillis)
      Cancellable(dom.clearTimeout(timeout))
    }
  }
}