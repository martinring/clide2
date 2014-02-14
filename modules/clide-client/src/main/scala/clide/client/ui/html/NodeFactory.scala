package clide.client.ui.html

import org.scalajs.dom._
import scala.language.implicitConversions
import clide.client.rx._
import clide.client.util.Cancellable
import clide.client.util.Buffer

trait InsertedNode {
  def detach()
  def remove()
  def insertBefore(t: Node)
  def replace(t: Node) = { insertBefore(t); remove() }
}

object InsertedNode {
  def apply(f: => (Node => Unit),c: => Unit, g: => Unit = ()) = new InsertedNode {
    def remove() = { g; c }
    def detach() = g
    def insertBefore(t: Node) = { f(t) }
  }
}

trait NodeFactory {
  def create(insert: Node => Unit): InsertedNode
}

object NodeFactory {
  def apply(c: (Node => Unit) => InsertedNode) = new NodeFactory {
    def create(insert: Node => Unit) = c(insert)
  }
  
  implicit def text(value: String) = NodeFactory { insert =>
    val node = document.createTextNode(value)
    insert(node)
    InsertedNode(newChild => node.parentNode.insertBefore(newChild, node), node.parentNode.removeChild(node))
  }
  
  implicit def observableText(value: Observable[String]) = NodeFactory { insert =>
    val node = document.createTextNode("")
    insert(node)
    val sub = value.observe(node.textContent = _)
    InsertedNode(newChild => node.parentNode.insertBefore(newChild,node), node.parentNode.removeChild(node), sub.cancel())    
  }
  
  implicit def observable(value: Observable[NodeFactory]) = NodeFactory { insert =>
    val node: Node = document.createComment("observableFactoryFactory")    
    insert(node)    
    var s = InsertedNode(newChild => node.parentNode.insertBefore(newChild, node), node.parentNode.removeChild(node))    
    val sub = value.observe(factory => s = factory.create(s.replace))   
    InsertedNode(s.replace(_), s.remove(), { s.detach(); sub.cancel() })
  }
    
  implicit def sequence(value: Seq[NodeFactory]) = NodeFactory { insert =>
    val node = document.createComment("emptyNodeSeq")
    insert(node)
    val last = InsertedNode(newChild => node.parentNode.insertBefore(newChild, node), node.parentNode.removeChild(node))
    if (value.length > 0) {      
      val all = value.map(_.create(last.insertBefore(_))) :+ last
      InsertedNode(all(0).insertBefore, all.map(_.remove()), all.map(_.detach()))
    } else {
      last
    }      
  }
  
  implicit def observableSequence(value: Observable[CollectionChange[NodeFactory]]) = NodeFactory { insert =>    
    val node: Node = document.createComment("observableSeqFactory-end")    
    insert(node)
    val last = InsertedNode(newChild => node.parentNode.insertBefore(newChild, node), node.parentNode.removeChild(node))
    val nodes = Buffer.apply[InsertedNode](last)
    val sub = value.observe({ msg => msg match {
      case Insert(Head,factory) =>                         
        nodes.+=:(factory.create(nodes.head.insertBefore(_)))       
      case Insert(Last,factory) =>
        nodes.insert(nodes.length - 1, factory.create(last.insertBefore(_)))        
      case Insert(Index(i), factory) =>        
        nodes.insert(i, factory.create(nodes(i).insertBefore(_)))
      case Remove(Head) =>
        nodes.remove(0).remove()
      case Remove(Last) =>
        nodes.remove(nodes.length - 2).remove()
      case Remove(Index(i)) =>
        nodes.remove(i).remove()        
      case Update(Head,factory) =>
        nodes(0) = factory.create(nodes(0).replace(_))
      case Update(Last,factory) =>
        nodes(nodes.length - 2) = factory.create(nodes(nodes.length - 2).replace(_))
      case Update(Index(i),factory) =>
        nodes(i) = factory.create(nodes(i).replace(_))        
      case Clear =>
        nodes.init.foreach(_.remove())
        nodes.remove(0, nodes.length - 1)
    }})
    
    InsertedNode(nodes(0).insertBefore(_), nodes.map((x: InsertedNode) => x.remove()), { sub.cancel(); nodes.map((x: InsertedNode) => x.detach()) })
  }  
}

class Tag[E <: Control](name: String, preset: BoundAttribute[E]*) {
  def apply(attributes: BoundAttribute[E]*)(children: NodeFactory*): NodeFactory = NodeFactory { insert =>
    val e = document.createElement(name)
    val p = preset.map(_.attach(e))
    val a = attributes.map(_.attach(e))
    insert(e)
    val all = children.map(_.create(e.appendChild(_)))
    InsertedNode(newChild => e.parentNode.insertBefore(newChild, e), e.parentNode.removeChild(e),
    {
      p.foreach(_.cancel())
      a.foreach(_.cancel())
      all.foreach(_.detach())
    })
  }
}