package clide.reactive

import scala.concurrent.ExecutionContext

trait Continuous[+A] {
  def get: A
}

object Continuous {
  def apply[A](f: => A) = new Continuous[A] {
    def get = f
  }
  
  def stepper[A](start: A)(event: Event[A])(implicit ec: ExecutionContext) = {
    var current = start
    event.foreach(current = _)
    Continuous(current)
  }
}