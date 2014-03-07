package clide.client.ui.html

import clide.client.rx._
import clide.client.util._
import scala.collection.mutable.Buffer

trait Var[T] extends Observable[T] {
  private [html] var getter: Option[() => T] = None
  private [html] var setter: Option[T => Unit] = None
  def :=(value: T)
  def get: T
  private [html] def update()
  def reset()
  
  /*def validate (f: T => Boolean, msg: => String) = new Var[T] {
    
  }*/
}

object Var {
  def apply[T](value: T) = new Var[T] {
    private val subscribers = Buffer.empty[Observer[T]]
    private var cache = value
        
    def reset() {
      cache = value
      subscribers.foreach(_.onNext(value))
    }
    
    def get = cache

    def update() {
      getter.map(_()).foreach { next => if (next != cache)
        subscribers.foreach(_.onNext(next))
        cache = next
      }
    }
    
    def :=(value: T) = {
      setter.foreach(_(value))
      if (value != cache) {
        subscribers.foreach(_.onNext(value))
        cache = value
      }
    }
    
    def observe(observer: Observer[T]): Cancellable = {
      subscribers += observer
      observer.onNext(cache)
      Cancellable(subscribers -= observer)
    }
  }
}