package clide.client.ui

abstract class Component extends NodeFactory {
  val template: NodeFactory
  def create() = template.create
}

