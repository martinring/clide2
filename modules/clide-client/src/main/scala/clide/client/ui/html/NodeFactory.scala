package clide.client.ui.html

import org.scalajs.dom._
import scala.language.implicitConversions
import clide.client.rx.Observable

trait NodeFactory {
  def create()(implicit parent: Node): Node
}

object NodeFactory {
  def apply(c: Node => Node) = new NodeFactory {
    def create()(implicit parent: Node) = c(parent)
  }
  
  implicit def textNodeFactory(value: String) = new NodeFactory {
    def create()(implicit parent: Node) = {
      val e = document.createTextNode(value)
      parent.elem.appendChild(e)
      Node(e.asInstanceOf[HTMLElement])()
    }
  }
  
  implicit def observableFactory(value: Observable[String]) = new NodeFactory {
    def create()(implicit parent: Node) = {
      val e = document.createTextNode("")      
      parent.elem.appendChild(e)
      val subscription = value.observe(e.textContent = _)
      Node(e.asInstanceOf[HTMLElement])(subscription.cancel())
    }
  }
}

class Tag[E <: Control](name: String, preset: BoundAttribute[_,E]*) {
  def apply(attributes: BoundAttribute[_,E]*)(children: NodeFactory*) = NodeFactory { parent =>
    val e = document.createElement(name)
    val p = preset.foreach(_.attach(e))
    val a = attributes.foreach(_.attach(e))
    val node = Node(e)()
    children.foreach(_.create()(node))
    parent.elem.appendChild(e)
    node
  }
}