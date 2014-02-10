package clide.client.ui

import clide.client.ui.html._

trait UserControl extends NodeFactory {
  val template: NodeFactory
  
  def create()(implicit parent: Node) = {
    template.create()(parent)
  }
}