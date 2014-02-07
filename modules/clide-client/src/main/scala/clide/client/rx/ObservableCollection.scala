package clide.client.rx

import scalajs.js

trait CollectionUpdate[T]
case class Init[T](items: js.Array[T]) extends CollectionUpdate[T]
case class Insert[T](index: Int, item: T) extends CollectionUpdate[T]
case class Remove[T](index: Int) extends CollectionUpdate[T]

class ObservableCollection[T] extends Observable[CollectionUpdate[T]] {
  private var underlying = js.Array[T]()
  
  private var observers = js.Array[Observer[CollectionUpdate[T]]]()
  
  def subscribe(observer: Observer[CollectionUpdate[T]]) = {
    observers.push(observer)
    observer.onNext(Init(underlying))
    Subscription{
      observers = observers.filter((o: Observer[CollectionUpdate[T]]) => o != observer)
    }
  }
  
  def length: Int = underlying.length.toInt
  def apply(index: Int) = underlying.apply(index)
  
  def insert(index: Int, item: T) = {
    underlying.splice(index, 0, item)
    observers.foreach(_.onNext(Insert(index,item)))
  }
      
  def remove(index: Int) = {
    underlying.splice(index, 1)
    observers.foreach(_.onNext(Remove(index)))
  }
}