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