//package clide.client.ec6
//
//import scala.scalajs.js
//import scala.scalajs.js.annotation.JSName
//
//@JSName("Set")
//object Set {
//}
//
//class Set[+A]() extends js.Object {
//  def length: Int = ???
//  private [ec6] def has(value: A): Boolean = ???
//  private [ec6] def add(value: A): this.type = ???
//  def clear(): Unit = ???
//  protected def delete(value: A): Boolean = ???
//  protected def forEach(callback: js.Function1[A,Unit]): Unit = ???
//  protected def values(): Iterator[A]
//}
//
//trait SetWrapper[+A] extends Set[A] with collection.mutable.Set[A] {
//  def contains(elem: A): Boolean = has(elem)
//  def iterator: collection.Iterator[A] = values()
//  def += (elem: A): this.type = add(elem)
//  def -= (elem: A): this.type = { delete(elem); this }
//}