package clide.client.rx

import clide.client.util.Buffer
import clide.client.util.Cancellable

trait Subject[T] extends Observable[T] with Observer[T] {
  def get: T
  def set(v: T) = onNext(v)
}

object Subject {
  def apply[T](initial: T) = new Subject[T] {
    private val subscribers = Buffer.empty[Observer[T]]
    private var cache = initial
    def get = cache    
    
    def observe(observer: Observer[T]): Cancellable = {
      subscribers += observer
      observer.onNext(cache)
      Cancellable(subscribers -= observer)
    }
    
    def onNext(next: T) = if (cache != next) {
      cache = next
      subscribers.foreach(_.onNext(next))
    }
    
    def onError(e: Throwable) = subscribers.foreach(_.onError(e))
    
    def onCompleted() = {
      subscribers.foreach(_.onCompleted())
      subscribers.clear()
    }
  }
}