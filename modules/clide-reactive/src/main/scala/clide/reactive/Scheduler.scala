package clide.reactive

import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.Promise
import scala.util.Try

trait Scheduler {
  def now: Long
  def schedule[A](duration: FiniteDuration)(task: => A): Ticket
  def scheduleOnce[A](duration: FiniteDuration)(task: => A): Ticket
  
  def timeout[A](duration: FiniteDuration): Future[Unit] = {
    val promise = Promise[Unit]
    schedule(duration)(promise.success(()))
    promise.future
  }
}