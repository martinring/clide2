package clide.reactive.ui.events

import org.scalajs.dom.EventTarget
import clide.reactive.Event
import scala.scalajs.js.Any.fromFunction1
import scala.scalajs.js.Any.fromString
import scala.concurrent.Future

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