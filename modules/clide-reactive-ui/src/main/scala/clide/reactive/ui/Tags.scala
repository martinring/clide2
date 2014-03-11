package clide.reactive.ui

import clide.reactive.ui.events._
import org.scalajs.dom.document

abstract class Tag(name: String) extends View with FormEvents with KeyboardEvents with MouseEvents {
  protected val elem = document.createElement(name)
  def eventTarget = elem
  
}