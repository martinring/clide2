package clide.reactive

import scala.collection.mutable.Buffer
import scala.concurrent.ExecutionContext
import scala.collection.mutable.ArrayBuffer

trait CollectionPosition
case object Head extends CollectionPosition
case object Last extends CollectionPosition
case class Index(n: Int) extends CollectionPosition

sealed trait CollectionUpdate[+A] {
  def map[B](f: A => B): CollectionUpdate[B]    
}
case class Insert[A](pos: CollectionPosition, value: A) extends CollectionUpdate[A] {
  def map[B](f: A => B) = Insert(pos,f(value))
}
case class Update[A](pos: CollectionPosition, value: A) extends CollectionUpdate[A] {
  def map[B](f: A => B) = Update(pos,f(value))
}
case class Remove(pos: CollectionPosition) extends CollectionUpdate[Nothing] {
  def map[B](f: Nothing => B): CollectionUpdate[B] = Remove(pos)
}
case object Reset extends CollectionUpdate[Nothing] {
  def map[B](f: Nothing => B): CollectionUpdate[B] = Reset
}

trait ObservableBufferView[A] { outer =>
  def changes(implicit ec: ExecutionContext): Event[CollectionUpdate[A]]
  def map[B](f: A => B) = new ObservableBufferView[B] {
    def changes(implicit ec: ExecutionContext): Event[CollectionUpdate[B]] =
      outer.changes.map(_.map(f))
  }
  def length(implicit ec: ExecutionContext): Event[Int] = changes.scan (0) { 
    case (n,Update(_,_)) => n
    case (n,Insert(_,_)) => n + 1
    case (n,Remove(_)) => n - 1
    case (n,Reset) => 0
  }
}

trait ObservableBuffer[A] extends Buffer[A] with ObservableBufferView[A] {
  private val channels = Buffer.empty[Channel[CollectionUpdate[A]]]
  
  def changes(implicit ec: ExecutionContext): Event[CollectionUpdate[A]] = {
    lazy val (event: Event[CollectionUpdate[A]], channel: Channel[CollectionUpdate[A]]) = 
      Event.broadcast(channels -= channel)
    channels += channel
    this.foreach(x => channel.push(Insert(Last,x)))
    event
  }
  
  def watch: ObservableBufferView[A] = this 
  
  abstract override def +=(element: A): this.type = {
    super.+=(element)
    channels.foreach(_.push(Insert(Last,element)))
    this
  }
  
  abstract override def ++=(xs: TraversableOnce[A]): this.type = {
    for (x <- xs) this += x
    this
  }
  
  abstract override def +=:(element: A): this.type = {
    super.+=:(element)
    channels.foreach(_.push(Insert(Head,element)))
    this
  }
  
  abstract override def update(n: Int, newelement: A): Unit = {
    super.update(n,newelement)
    channels.foreach(_.push(Update(Index(n),newelement)))
  }
  
  abstract override def remove(n: Int): A = {
    val elem = super.remove(n)
    channels.foreach(_.push(Remove(Index(n))))
    elem
  }
  
  def replaceAll(all: TraversableOnce[A]): Unit = {    
    val remove = this.clone()
    all.foreach { a =>
      remove.indexOf(a) match {
        case -1 => this += a
        case i  => remove.remove(i)
      }
    }
    remove.foreach { x =>
      this.remove(indexOf(x))
    }
  }
  
  abstract override def clear(): Unit = {
    super.clear()
    channels.foreach(_.push(Reset))
  }
  
  abstract override def insertAll(n: Int, elems: Traversable[A]) {
    super.insertAll(n,elems)
    var i = 0
    elems.foreach { elem =>
      channels.foreach(_.push(Insert(Index(n + i), elem)))
      i += 1
    }
  }
}

object ObservableBuffer {
  def empty[A]: ObservableBuffer[A] = new ArrayBuffer[A] with ObservableBuffer[A]
  def apply[A](elems: A*): ObservableBuffer[A] = empty[A] ++= elems
}