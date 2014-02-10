package clide.client.util

import scalajs.js

class Buffer[A] private[util] (private val underlying: js.Array[A]) {
  def +=(elem: A): Buffer.this.type = { underlying.push(elem); this }
  def +=:(elem: A): Buffer.this.type = { underlying.unshift(elem); this }
  def apply(n: Int): A = underlying.apply(n)
  def clear(): Unit = underlying.splice(0)
  def insertAll(n: Int, elems: Buffer[A]): Unit = underlying.asInstanceOf[js.Dynamic].splice.apply(n, 0, elems.underlying)
  def iterator: Iterator[A] = new Iterator[A] {
    var index = 0
    def hasNext: Boolean = underlying.length > index
    def next(): A = {
      val result = underlying(index)
      index += 1
      result
    }
  } 
  def length: Int = underlying.length.asInstanceOf[Int]
  def remove(n: Int): A = underlying.splice(n,1).apply(0)
  def update(n: Int, newelem: A): Unit = underlying.update(n, newelem)
  
  def ++(that: Buffer[A]): Buffer[A] = new Buffer(underlying.concat(that.underlying))
  def ++=(that: Buffer[A]): Buffer.this.type = 
    { underlying.asInstanceOf[js.Dynamic].push.apply(that.underlying); this }
  def -=(elem: A): Buffer[A] = 
    { underlying.splice(underlying.indexOf(elem),1); this }
  def distinct: Buffer[A] = {
    var u = js.Object()
    var a = js.Array[A]()
    for (i <- 0 to underlying.length.asInstanceOf[Int]) {
      if (!u.hasOwnProperty(this.apply(i).asInstanceOf[String])) {
        a.push(this.apply(i))
        u.asInstanceOf[js.Array[Boolean]].update(this.apply(i).asInstanceOf[js.Number],true)
      }
    }
    new Buffer(a)
  }
  def head: A = underlying.apply(0)
  def headOption: Option[A] = if (underlying.length > 0) Some(underlying.apply(0)) else None
  def indexOf(elem: A): Int = underlying.indexOf(elem).asInstanceOf[Int]
  def isEmpty: Boolean = underlying.length == 0
  def init: Buffer[A] = new Buffer(underlying.slice(0,underlying.length - 1))
  def tail: Buffer[A] = new Buffer(underlying.slice(1))
  def foreach(f: A => Unit) = underlying.forEach((a: (A,js.Number,js.Array[A])) => f(a._1))
  //def map[B](f: A => B): Buffer[A] = new Buffer(underlying.map[B]((a: (A,js.Number,js.Array[A])) => f(a._1)))
  //def flatMap[B](f: A => Buffer[B]) = map(f).underlying
}

object Buffer {
  def empty[A]: Buffer[A] = new Buffer(js.Array())
  def apply[A](elems: A*): Buffer[A] = new Buffer(js.Array(elems: _*))
}