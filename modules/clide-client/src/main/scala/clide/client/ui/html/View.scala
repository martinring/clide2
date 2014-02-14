package clide.client.ui.html

import clide.client.ui.html._
import org.scalajs.dom.Node
import clide.client.rx.Observable
import clide.client.ui.html.NodeFactory.observable

trait DataView[T] extends View {
  val data: Observable[T]
  def render(data: T): NodeFactory
  def template: NodeFactory = data.map(render)
}

trait View extends NodeFactory {
  def template: NodeFactory
  
  def create(insert: Node => Unit) = {
    template.create(insert)
  }
}