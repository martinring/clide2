package clide.reactive.ui.events

import org.scalajs.dom._

trait KeyboardEvents {
  def eventTarget: EventTarget
  def keydown = DOMEvent[KeyboardEvent](eventTarget,"keydown")
  def keypress = DOMEvent[KeyboardEvent](eventTarget,"keypress")
  def keyup = DOMEvent[KeyboardEvent](eventTarget,"keyup")  
}