package clide.reactive.ui.html

import scalajs.js

object HTMLElement {
  def unapply(elem: Any): Option[String] = elem match {
    case elem: org.scalajs.dom.HTMLElement => 
      Some(elem.nodeName)
    case _ => None
  }
}