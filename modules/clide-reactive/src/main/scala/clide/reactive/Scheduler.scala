package clide.reactive

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

object BlockingScheduler extends Scheduler {
  import scala.concurrent.ExecutionContext.Implicits.global
  
  def now: Long = System.currentTimeMillis()
  def schedule[A](duration: FiniteDuration)(task: => A): Cancellable = {
    var cancelled = false
    Future {
      Thread.sleep(duration.toMillis)
      while (!cancelled) {
        Future(task)
        Thread.sleep(duration.toMillis)
      }
    }
    Cancellable(cancelled = true)
  }
  
  def scheduleOnce[A](duration: FiniteDuration)(task: => A): Cancellable = {
    var cancelled = false
    Future {
      Thread.sleep(duration.toMillis)
      if (!cancelled) task      
    }
    Cancellable(cancelled = true)
  }
  
}