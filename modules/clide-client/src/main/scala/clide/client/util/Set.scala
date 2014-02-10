package clide.client.util

class Set[A] extends scala.collection.mutable.Set[A] {
  def contains(key: A): Boolean
  def iterator: Iterator[A]
  def +=(elem: A): Set.this.type
  def -=(elem: A): Set.this.type
}