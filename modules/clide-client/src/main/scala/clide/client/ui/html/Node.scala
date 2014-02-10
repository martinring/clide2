package clide.client.ui.html

import org.scalajs.dom._

trait Node {
  private [html] val elem: HTMLElement
  def dispose()
}

object Node {
  private [html] def apply(e: HTMLElement)(d: => Unit): Node = new Node {
    private [html] val elem = e
    def dispose() = d
  }
}

object BodyNode extends Node {
  private [html] val elem: HTMLElement = document.body 
  def dispose() = { }
}