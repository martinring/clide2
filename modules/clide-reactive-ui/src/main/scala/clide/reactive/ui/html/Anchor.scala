package clide.reactive.ui.html

import scalajs.js
import org.scalajs.dom

object Anchor {
  def unapply(a: Any): Option[dom.HTMLAnchorElement] = a match {
    case HTMLElement("A") => Some(a.asInstanceOf[dom.HTMLAnchorElement])
    case _ => None
  }
}