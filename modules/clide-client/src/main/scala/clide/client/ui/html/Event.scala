package clide.client.ui.html

import clide.client.rx._
import clide.client.util.Cancellable
import org.scalajs.dom.EventTarget

trait Event[T,-E <: Control] {
  def attach(target: Any, observer: Observer[T]): Cancellable
  
  def --> (f: => Unit) = BoundAttribute(a => attach(a,Observer(_ => f))) 
}

object Event {
  def apply[T,E <: Control](name: String) = new Event[T,E] {
    def attach(target: Any, observer: Observer[T]): Cancellable =
      Observable.fromEvent(target.asInstanceOf[EventTarget], name).observe(observer)
  }
  
  def once = new Event[Unit,Control] {
    def attach(target: Any, observer: Observer[Unit]): Cancellable =
      Observable.from(()).observe(observer)
  }
}