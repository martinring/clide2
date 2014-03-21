package clide.reactive.ui

import org.scalajs.dom.Node

trait InsertionContext {
  def insert(node: Node): InsertedNode
}

object InsertionContext {
  def apply(action: Node => Unit): InsertionContext = new InsertionContext {
    def insert(node: Node): InsertedNode = {
      action(node)
      InsertedNode(node)
    }
  }
  
  def append(parent: Node) =
    InsertionContext(parent.appendChild)
  
  def before(ref: Node) =
    InsertionContext(ref.parentNode.insertBefore(_, ref))
  
  def replace(old: Node) =
    InsertionContext(old.parentNode.replaceChild(_, old))
}

trait InsertedNode { 
  def before: InsertionContext
  def replace: InsertionContext
  def remove()
}

object InsertedNode {
  def apply(node: Node) = new InsertedNode {
    def before = InsertionContext.before(node)
    def replace = InsertionContext.replace(node)
    def remove() = node.parentNode.removeChild(node)
  }
}