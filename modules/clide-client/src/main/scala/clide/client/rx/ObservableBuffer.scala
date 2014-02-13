package clide.client.rx

import scala.collection.mutable.Buffer
import clide.client.util.Cancellable

sealed trait Location
object Head extends Location
object Last extends Location
case class Index(n: Int) extends Location

sealed trait CollectionChange[+A] {
  def map[B](f: A => B): CollectionChange[B] = this match {
    case Insert(l,e) => Insert(l,f(e))
    case Update(l,e) => Update(l,f(e))
    case Remove(l) => Remove(l)
    case Clear => Clear    
  }
}
case class Insert[A](loc: Location, elem: A) extends CollectionChange[A]
case class Update[A](loc: Location, elem: A) extends CollectionChange[A]
case class Remove[A](loc: Location) extends CollectionChange[A]
case object Clear extends CollectionChange[Nothing]

trait ObservableBuffer[A] extends Buffer[A] {
  def observable: Observable[CollectionChange[A]]
}

trait ObservableCollection[A] extends Observable[CollectionChange[A]] {
  def mapChanges[B](f: A => B): Observable[CollectionChange[B]] = this.map((c: CollectionChange[A]) => c.map(f)) 
}

object ObservableBuffer {
  def fromBuffer[A](buffer: Buffer[A]) = new ObservableBuffer[A] {
    private var subscribers = clide.client.util.Buffer.empty[Observer[CollectionChange[A]]]
    val observable = new ObservableCollection[A] {
      def observe(observer: Observer[CollectionChange[A]]): Cancellable = {
        subscribers += observer
        buffer.foreach(elem => observer.onNext(Insert(Last,elem)))
        Cancellable(subscribers -= observer)
      }
    }
    
    def +=(elem: A): this.type = {      
      buffer += elem
      subscribers.foreach(_.onNext(Insert(Last,elem)))
      this
    }

    def +=:(elem: A): this.type = {
      elem +=: buffer
      subscribers.foreach(_.onNext(Insert(Head,elem)))
      this
    }

    def apply(n: Int): A = buffer.apply(n)    

    def clear(): Unit = {
      buffer.clear()
      subscribers.foreach(_.onNext(Clear))
    }

    def insertAll(n: Int, elems: collection.Traversable[A]): Unit = {
      buffer.insertAll(n,elems)
      var index = n
      for {
        elem <- elems        
      } {        
        subscribers.foreach(_.onNext(Insert(Index(index),elem)))
        index += 1
      }
    }

    def iterator: Iterator[A] = buffer.iterator

    def length: Int = buffer.length 
    
    def remove(n: Int): A = {
      val elem = buffer.remove(n)
      subscribers.foreach(_.onNext(Remove(Index(n))))
      elem
    }

    def update(n: Int, newelem: A): Unit = {
      buffer.update(n,newelem)
      subscribers.foreach(_.onNext(Update(Index(n), newelem)))      
    }
  }
}