package clide.reactive.ui

import org.scalajs.dom.Node

trait InsertionContext {
  def insert(node: Node): InsertionContext with Inserted
}

trait Inserted extends InsertionContext { 
  def before: InsertionContext
  def after: InsertionContext
  def remove()
}