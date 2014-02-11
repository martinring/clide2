package clide.client.ui.html

import clide.client.rx._
import clide.client.util.Cancellable
import org.scalajs.dom.EventTarget

trait Event[T,-E <: Control] {
  def attach(target: Any): Observable[T]
  
  def triggers(action: Action) = BoundAttribute[E]{ x => attach(x).observe(_ => action.trigger()) }
  def updates[T](v: Var[T]) = BoundAttribute[E]{ x => attach(x).observe(_ => v.update() ) }
  
  def map[U](f: T => U) = Event[U,E]{ x => attach(x).map(f) }
  def flatMap[U](f: T => Observable[U]) = Event[U,E]{ x => attach(x).flatMap(f) }
  def filter(f: T => Boolean) = Event[T,E]{ x => attach(x).filter(f) }
  def foreach(f: T => Unit) = BoundAttribute{ x => attach(x).foreach(f) }
}

object Event {
  def apply[T,E <: Control](a: Any => Observable[T]) = new Event[T,E] {
    def attach(target: Any) = a(target)
  }
  
  def named[T,E <: Control](name: String) = new Event[T,E] {
    def attach(target: Any): Observable[T] =
      Observable.fromEvent(target.asInstanceOf[EventTarget], name)
  }
  
  def once = new Event[Unit,Control] {
    def attach(target: Any): Observable[Unit] =
      Observable.from[Unit](())
  }
}