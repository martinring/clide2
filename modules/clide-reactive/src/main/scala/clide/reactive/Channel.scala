package clide.reactive

import scala.concurrent.Future

trait Channel[-A] {
  def push(a: => A): Future[Unit]
  def failure(e: Throwable)
  def close()
}

object Channel {
  def apply[A](f: A => Future[Unit])(e: Throwable => Unit)(c: => Unit) = new Channel[A] {
    def push(a: => A) = f(a)
    def failure(t: Throwable) = e(t)
    def close() = c
  }
}