package clide.reactive

import scala.util.control.NonFatal

sealed trait Reactive[A] {  
  def step(value: A): Reactive[A]
}

object Reactive {
  def scanner[A,B](start: => B)(f: (B,A) => B): Reactive[A] = new Reactive[A] {
    def step(value: A) = scanner(f(start,value))(f)
  }
  
  def apply[A](f: A => Reactive[A]) = new Reactive[A] {
    def step(value: A) = f(value)
  }
}