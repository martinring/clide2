package clide.reactive.ui

import scalajs.js
import org.scalajs.dom
import clide.reactive.Event

trait JSApp extends DelayedInit {
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.runNow
  implicit val scheduler = clide.reactive.ui.Scheduler
  
  def title: String = dom.document.title
  def title_=(value: String) = {
    dom.document.title = value
    dom.history.replaceState(dom.history.state, value, dom.location.pathname)
  }
  
  def delayedInit(body: => Unit) = {
    val idempbody = { 
      var initialized = false
      () => if (!initialized) {
        initialized = true
        body
      }
    }
    dom.document.addEventListener("DOMContentLoaded", (e: dom.Event) => idempbody())
  }
}