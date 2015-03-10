package clide.reactive

import scala.collection.mutable.Buffer
import scala.concurrent.ExecutionContext
import scala.collection.mutable.ArrayBuffer

trait CollectionPosition
case object Last extends CollectionPosition
case class Index(n: Int) extends CollectionPosition

sealed trait CollectionUpdate[+A] {
  def map[B](f: A => B): CollectionUpdate[B]    
}
case class Insert[A](pos: CollectionPosition, next: A) extends CollectionUpdate[A] {
  def map[B](f: A => B) = Insert(pos,f(next))
}
case class Update[A](pos: CollectionPosition, prev: A, next: A) extends CollectionUpdate[A] {
  def map[B](f: A => B) = Update(pos,f(prev),f(next))
}
case class Remove[A](pos: CollectionPosition, prev: A) extends CollectionUpdate[A] {
  def map[B](f: A => B): CollectionUpdate[B] = Remove(pos,f(prev))
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
    case (n,Update(_,_,_)) => n
    case (n,Insert(_,_)) => n + 1
    case (n,Remove(_,_)) => n - 1
    case (n,Reset) => 0
  }
  
  def count(f: A => Boolean)(implicit ec: ExecutionContext): Event[Int] = changes.scan (0) {
    case (n,Update(_,prev,next)) => 
      n + (if (f(prev)) -1 else 0) + (if (f(next)) 1 else 0)
    case (n,Insert(_,next)) => 
      n + (if (f(next)) 1 else 0)
    case (n,Remove(_,prev)) => 
      n - (if (f(prev)) 1 else 0)
    case (_,Reset) =>
      0
  }
  
  def toStrings(implicit ec: ExecutionContext): ObservableBufferView[String] = map(_.toString)
}

trait ObservableBuffer[A] extends Buffer[A] with ObservableBufferView[A] {
  private val channels = Buffer.empty[Channel[CollectionUpdate[A]]]
  
  def changes(implicit ec: ExecutionContext): Event[CollectionUpdate[A]] = {
    lazy val (event, channel: Channel[CollectionUpdate[A]]) = 
      Event.broadcast[CollectionUpdate[A]](channels -= channel)
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
    channels.foreach(_.push(Insert(Index(0),element)))
    this
  }
  
  abstract override def update(n: Int, newelement: A): Unit = {
    super.lift(n) match {
      case None =>
        super.insert(n,newelement)
        channels.foreach(_.push(Insert(Index(n),newelement)))
      case Some(old) =>
        super.update(n, newelement)
        channels.foreach(_.push(Update(Index(n),old,newelement)))
    }
  }
  
  abstract override def remove(n: Int): A = {
    val elem = super.remove(n)
    channels.foreach(_.push(Remove(Index(n),elem)))
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
  
  def clear(filter: A => Boolean): Unit = {
    replaceAll(super.filter(filter))
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