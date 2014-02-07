package clide.client.ui

trait DataTemplate[T] {
  val data: T
  val template: NodeFactory
}