package clide.client.ui.html

import org.scalajs.dom._
import scala.language.implicitConversions
import clide.client.rx._
import clide.client.util.Cancellable
import clide.client.util.Buffer

trait NodeFactory {
  def create(insert: Node => Unit): Cancellable
}

object NodeFactory {
  def apply(c: (Node => Unit) => Cancellable) = new NodeFactory {
    def create(insert: Node => Unit) = c(insert)
  }
  
  implicit def textNodeFactory(value: String) = NodeFactory { insert =>
    insert(document.createTextNode(value))
    Cancellable()
  }
  
  implicit def observableStringFactory(value: Observable[String]) = NodeFactory { insert =>
    val e = document.createTextNode("")
    insert(e)
    value.observe(e.textContent = _)
  }
  
  implicit def observableFactoryFactory(value: Observable[NodeFactory]) = NodeFactory { insert =>
    var node: Node = document.createComment("placeholder")    
    insert(node)
    
    var s = Cancellable()
    
    value.observe({ factory =>
      s.cancel()
      s = factory.create { newNode => 
        node.parentNode.replaceChild(newNode, node)
        node = newNode
      }
    }) and s
  }
  
  implicit def observableSeqFactory(value: Observable[CollectionChange[NodeFactory]]) = NodeFactory { insert =>    
    val last: Node = document.createComment("repeat-end")    
    insert(last)
    val nodes = Buffer.empty[Node]
    val cs = Buffer.empty[Cancellable]
    value.observe({ msg => msg match {
      case Insert(Head,factory) =>
        val n = nodes.headOption.getOrElse(last)                  
        cs.+=:(factory.create { node =>
          n.parentNode.insertBefore(node, n)
          nodes.+=:(node)         
        })       
      case Insert(Last,factory) =>
        cs += factory.create { node =>
          last.parentNode.insertBefore(node, last)
          nodes += node
        }
      case Insert(Index(i), factory) =>
        val n = nodes.lift(i).getOrElse(last)
        cs.insert(i,factory.create { node =>
          n.parentNode.insertBefore(node, n)
          nodes.insert(i, node)
        })
      case Remove(Head) =>
        val n = nodes.remove(0)
        val c = cs.remove(0)
        c.cancel()
        n.parentNode.removeChild(n)
      case Remove(Last) =>
        val n = nodes.remove(nodes.length - 1)
        val c = cs.remove(nodes.length - 1)
        c.cancel()
        n.parentNode.removeChild(n)
      case Remove(Index(i)) =>
        val n = nodes.remove(i)
        val c = cs.remove(i)
        c.cancel()
        n.parentNode.removeChild(n)        
      case Update(Head,factory) =>
        val n = nodes(0)
        val c = cs(0)
        c.cancel()
        cs(0) = factory.create{ node => 
          nodes(0) = node
          n.parentNode.replaceChild(node, n)          
        }
      case Update(Last,factory) =>
        val i = nodes.length - 1
        val n = nodes.remove(i)
        val c = cs.remove(i)
        c.cancel()
        cs(i) = factory.create{ node => 
          nodes(i) = node
          n.parentNode.replaceChild(node, n)          
        }
      case Update(Index(i),factory) =>
        val n = nodes.remove(i)
        val c = cs.remove(i)
        c.cancel()
        cs(i) = factory.create{ node => 
          nodes(i) = node
          n.parentNode.replaceChild(node, n)          
        }        
      case Clear =>
        cs.foreach(_.cancel())
        nodes.foreach(n => n.parentNode.removeChild(n))
        cs.clear()
        nodes.clear()
    }})         
  }
  
  implicit def nodeFactorySeq(value: Seq[NodeFactory]) = NodeFactory { insert =>    
    val all = value.map(_.create(insert)) // FIXME: only one call to insert
    Cancellable(all.foreach(_.cancel()))
  }
}

class Tag[E <: Control](name: String, preset: BoundAttribute[E]*) {
  def apply(attributes: BoundAttribute[E]*)(children: NodeFactory*): NodeFactory = NodeFactory { insert =>
    val e = document.createElement(name)
    val p = preset.map(_.attach(e))
    val a = attributes.map(_.attach(e))
    insert(e)
    val all = children.map(_.create(e.appendChild(_)))    
    Cancellable {
      p.foreach(_.cancel())
      a.foreach(_.cancel())
      all.foreach(_.cancel())
    }
  }
}