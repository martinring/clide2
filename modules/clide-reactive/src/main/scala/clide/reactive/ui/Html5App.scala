package clide.reactive.ui

import scalajs.js
import org.scalajs.dom
import clide.reactive.Event
import clide.reactive.ui.events.DOMEvent

trait Html5App extends DelayedInit {
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.runNow
  
  private val root = InsertionContext.append(dom.document)
  
  def render: View
  
  def online = Event.flipFlop(DOMEvent(dom.window,"online"),DOMEvent(dom.window,"offline"))
  
  def delayedInit(body: => Unit) =
    if (dom.document.readyState.asInstanceOf[String] == "completed"
     || dom.document.readyState.asInstanceOf[String] == "interactive") {
      body
      render(root)
    } else DOMEvent[dom.Event](dom.window, "readystatechange")
      .sample(dom.document.readyState.asInstanceOf[String])
      .exists(state => state == "completed" || state == "interactive")
      .foreach{ _ => body; render(root) }  
}