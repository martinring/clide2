package clide.client.util

import scalajs.js
import scala.language.implicitConversions

class Buffer[A] private[util] (private val underlying: js.Array[A]) extends Seq[A] {
  def +=(elem: A): Buffer.this.type = { 
    underlying.push(elem);
    
    this 
  }
  
  def +=:(elem: A): Buffer.this.type = { 
    underlying.unshift(elem);
    this 
  }
  
  def apply(n: Int): A = 
    underlying.apply(n)
  
  def clear(): Unit = 
    underlying.splice(0)
    
  override def clone(): Buffer[A] =
    new Buffer[A](underlying.slice(0))
    
  def collect[B](pf: PartialFunction[A,B]): Buffer[B] = {
    val result = js.Array[B]()
    foreach { a: A => if (pf.isDefinedAt(a)) result.push(pf(a)) }
    new Buffer(result)
  }
  
  override def contains(elem: Any): Boolean =
    underlying.indexOf(elem.asInstanceOf[A]) >= 0
      
    
  def insertAll(n: Int, elems: Buffer[A]): Unit = 
    underlying.asInstanceOf[js.Dynamic].splice.apply(n, 0, elems.underlying)
    
  def iterator: Iterator[A] = new Iterator[A] {
    var index = 0
    def hasNext: Boolean = underlying.length > index
    def next(): A = {
      val result = underlying(index)
      index += 1
      result
    }
  } 
  
  def length: Int = 
    underlying.length.asInstanceOf[Int]
  
  def remove(n: Int): A = 
    underlying.splice(n,1).apply(0)
    
  def removeHead: A =
    underlying.shift()
    
  def removeLast: A =
    underlying.pop()
    
  def update(n: Int, newelem: A): Unit = 
    underlying.update(n, newelem)
  
  def ++(that: Buffer[A]): Buffer[A] = 
    new Buffer(underlying.concat(that.underlying))
  
  def ++=(that: Buffer[A]): Buffer.this.type = { 
    underlying.asInstanceOf[js.Dynamic].push.apply(that.underlying); 
    this 
  }
  
  def -=(elem: A): Buffer[A] = { 
    underlying.splice(underlying.indexOf(elem),1); 
    this 
  }
  
  override def distinct: Buffer[A] = {
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
  
  override def head: A = 
    underlying.apply(0)
    
  override def headOption: Option[A] = 
    if (underlying.length > 0) Some(underlying.apply(0)) else None
    
  override def indexOf[B >: A](elem: B): Int = 
    underlying.indexOf(elem.asInstanceOf[A]).asInstanceOf[Int]
  
  override def isEmpty: Boolean = 
    underlying.length.asInstanceOf[Int] == 0
    
  override def init: Buffer[A] = 
    new Buffer(underlying.slice(0,underlying.length - 1))
  
  override def tail: Buffer[A] = 
    new Buffer(underlying.slice(1))
  
  override def foreach[U](f: A => U): Unit = {
    def jsf(a: A, i: js.Number, o: js.Array[A]) = f(a)
    underlying.forEach(jsf _)
  }         
    
  def map[B](f: A => B): Buffer[B] = {
    def jsf(a: A, i: js.Number, o: js.Array[A]) = f(a)
    new Buffer(underlying.map(jsf _))
  }       
  
  override def nonEmpty: Boolean =
    underlying.length > 0
    
  def flatMap[B](f: A => Buffer[B]): Buffer[B] = {
    def jsf(a: A, i: js.Number, o: js.Array[A]) = f(a)
    new Buffer[B](js.Dynamic.global.Array.prototype.concat.apply(js.Array[B](),underlying.map(jsf _)).asInstanceOf[js.Array[B]])
  }
  
  
}

object Buffer {
  def empty[A]: Buffer[A] = new Buffer(js.Array())
  def apply[A](elems: A*): Buffer[A] = new Buffer(js.Array(elems: _*))
  
  implicit def fromJsArray[T](arr: js.Array[T]) = new Buffer(arr)
}