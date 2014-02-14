package clide.client.ui.html

import org.scalajs.dom._
import clide.client.rx.Observable

object Mouse {
  val click = Observable.fromEvent[MouseEvent](window,"click")
  val move  = Observable.fromEvent[MouseEvent](window,"move")
}