package clide.reactive.ui

import clide.reactive.Event
import org.scalajs.dom.EventTarget

object DOMEvent {
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.runNow
  
  def apply[E](target: EventTarget, name: String): Event[E] = Event.fromCallback[E] { handler =>
    val listener: org.scalajs.dom.Event => Unit = ( event => handler(event.asInstanceOf[E]) )
    val jsListener: scalajs.js.Function1[org.scalajs.dom.Event,Unit] = listener
    println("register " + name)
    target.addEventListener(name, jsListener)
    () => {
      println("remove " + name)
      target.removeEventListener(name, jsListener)
    }
  }
}