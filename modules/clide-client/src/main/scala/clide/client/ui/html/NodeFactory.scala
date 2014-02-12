package clide.client.ui.html

import org.scalajs.dom._
import scala.language.implicitConversions
import clide.client.rx.Observable
import clide.client.util.Cancellable

trait InsertionContext {
  def insert(child: Node)  
  def insertReplacable(child: Node): InsertionContext
}

object InsertionContext {      
  def apply(node: Node): InsertionContext = new InsertionContext {        
    def insert(child: Node) { node.appendChild(child) }
    
    def insertReplacable(child: Node): InsertionContext = {
      insert(child)
      var last = child      
      new InsertionContext {      
        def insert(child: Node) { node.replaceChild(child, last); last = child }
        def insertReplacable(child: Node): InsertionContext = { insert(child); this }
      }
    }
  }
  
  def body = InsertionContext(document.body)
}

trait NodeFactory {
  def create(context: InsertionContext): Cancellable
}

object NodeFactory {
  def apply(c: InsertionContext => Cancellable) = new NodeFactory {
    def create(context: InsertionContext) = c(context)
  }
  
  implicit def textNodeFactory(value: String) = NodeFactory { context =>
    context.insert(document.createTextNode(value))
    Cancellable()
  }
  
  implicit def observableStringFactory(value: Observable[String]) = NodeFactory { context =>
    val e = document.createTextNode("")
    context.insert(e)
    value.observe(e.textContent = _)
  }
  
  implicit def observableFactoryFactory(value: Observable[NodeFactory]) = NodeFactory { context =>
    val init: Node = document.createTextNode("placeholder")
    val c = context.insertReplacable(init)
    var s = Cancellable()
    value.observe({ factory =>
      s.cancel()
      s = factory.create(c)
    })
  }
  
  implicit def nodeFactorySeq(value: Seq[NodeFactory]) = NodeFactory { context =>    
    val all = value.map(_.create(context))
    Cancellable(all.foreach(_.cancel()))
  }
}

class Tag[E <: Control](name: String, preset: BoundAttribute[E]*) {
  def apply(attributes: BoundAttribute[E]*)(children: NodeFactory*): NodeFactory = NodeFactory { context =>
    val e = document.createElement(name)
    val p = preset.map(_.attach(e))
    val a = attributes.map(_.attach(e))
    context.insert(e)
    val all = children.map(_.create(InsertionContext(e)))    
    Cancellable {
      p.foreach(_.cancel())
      a.foreach(_.cancel())
      all.foreach(_.cancel())
    }
  }
}