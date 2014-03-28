package clide.reactive.ui.events

import org.scalajs.dom._

trait MouseEvents {
  def eventTarget: EventTarget
  def click = DOMEvent[MouseEvent](eventTarget,"click")
  def dblclick = DOMEvent[MouseEvent](eventTarget,"dblclick")
  def drag = DOMEvent[DragEvent](eventTarget,"drag")
  def dragend = DOMEvent[DragEvent](eventTarget,"dragend")
  def dragenter = DOMEvent[DragEvent](eventTarget,"dragenter")
  def dragleave = DOMEvent[DragEvent](eventTarget,"dragleave")
  def dragover = DOMEvent[DragEvent](eventTarget,"dragover")
  def dragstart = DOMEvent[DragEvent](eventTarget,"dragstart")
  def drop = DOMEvent[DragEvent](eventTarget,"drop")
  def mousedown = DOMEvent[MouseEvent](eventTarget,"mousedown")
  def mousemove = DOMEvent[MouseEvent](eventTarget,"mousemove")
  def mouseout = DOMEvent[MouseEvent](eventTarget,"mouseout")
  def mouseover = DOMEvent[MouseEvent](eventTarget,"mouseover")
  def mouseup = DOMEvent[MouseEvent](eventTarget,"mouseup")
  def mousewheel = DOMEvent[MouseEvent](eventTarget,"mousewheel")
  def scroll = DOMEvent[MouseEvent](eventTarget,"scroll")
}