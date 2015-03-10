package clide.reactive.ui.html

import scalajs.js
import org.scalajs.dom.html

object Anchor {
  def unapply(a: Any): Option[html.Anchor] = a match {
    case HTMLElement("A") => Some(a.asInstanceOf[html.Anchor])
    case _ => None
  }
}