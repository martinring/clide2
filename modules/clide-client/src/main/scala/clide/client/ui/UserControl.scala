package clide.client.ui

import clide.client.ui.html._
import org.scalajs.dom.Node

trait UserControl extends NodeFactory {
  val template: NodeFactory
  
  def create(insert: Node => Unit) = {
    template.create(insert)
  }
}