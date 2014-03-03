package clide.reactive

import scala.concurrent.ExecutionContext

trait Slot[-A] {
  def << (value: Event[A]): Unit
}

trait Readable[+A] {
  def get: A
}

object Slot {
  def apply[A](f: A => Unit)(implicit ec: ExecutionContext) = new Slot[A] {
    def << (value: Event[A]) = value.foreach(f)
  }  
  
  def apply[A](f: A => Unit, read: => A)(implicit ec: ExecutionContext) = new Slot[A] with Readable[A] {
    def << (value: Event[A]) = value.foreach(f)
    def get: A = read
  }
}