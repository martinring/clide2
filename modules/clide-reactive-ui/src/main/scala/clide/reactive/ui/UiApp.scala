package clide.reactive.ui

import scalajs.js
import org.scalajs.dom
import clide.reactive.Event

trait UiApp extends DelayedInit {
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.runNow
  implicit val scheduler = clide.reactive.ui.UiScheduler

  //def online: Event[Boolean] = dom.navigator.onLine +: Event.flipFlop(dom.window on "online", dom.window on "offline")
  
  def delayedInit(body: => Unit) =
    (() +: DOMEvent(dom.window, "readystatechange"))
      .sample(dom.document.readyState.asInstanceOf[String])
      .exists(state => state == "complete" || state == "interactive")
      .foreach{ _ => println("initializing"); body; }  
}