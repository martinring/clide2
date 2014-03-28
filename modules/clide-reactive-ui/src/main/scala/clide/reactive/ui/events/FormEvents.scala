package clide.reactive.ui.events

import org.scalajs.dom._

trait FormEvents {
  def eventTarget: EventTarget
  def focus = DOMEvent[FocusEvent](eventTarget,"focus")
  def blur = DOMEvent[FocusEvent](eventTarget,"blur")  
  def formchange = DOMEvent[Event](eventTarget,"formchange")
  def forminput = DOMEvent[Event](eventTarget,"forminput")  
  def input = DOMEvent[Event](eventTarget,"input")
  def invalid = DOMEvent[Event](eventTarget,"invalid")
}
