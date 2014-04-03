package clide.reactive.ui

import clide.reactive.Event
import clide.reactive.EventSource
import scala.concurrent.ExecutionContext

trait Settable[A] {
  def := (value: A)
}

trait Bindable[A] extends Settable[A] {
  def get: A  
  def watch(implicit ec: ExecutionContext): Event[A]
}

object Var {
  def apply[A](init: A) = new Bindable[A] with EventSource[A] {
    private var current = init    
    def get = current
    def := (next: A) = {
      if (current != next)
        trigger(next)
      current = next
    }
    def watch(implicit ec: ExecutionContext) = register(current)
  }    
}