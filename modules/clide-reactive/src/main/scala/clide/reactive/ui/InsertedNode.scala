package clide.reactive.ui

import org.scalajs.dom.Node

private [ui] trait InsertedNode {
  def replace(node: Node)
  def remove()
  def insertBefore(node: Node)
}