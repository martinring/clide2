package clide.client.rx

import scala.collection.mutable.Buffer
import clide.client.util.Cancellable

trait Subject[T] extends Observable[T] with Observer[T] { self =>
  def pull(obs: () => T) = new PullSubject[T] {
    def observe(observer: Observer[T]): Cancellable = self.observe(observer)
    def onNext(next: T) = self.onNext(next)
    def onError(e: Throwable) = self.onError(e)
    def onCompleted() = self.onCompleted()
    def get: Option[T] = None
  }
}

trait PullSubject[T] extends Subject[T] {
  def get: Option[T]
}

object Subject {
  def empty[T] = new Subject[T] {
    private val subscribers = Buffer.empty[Observer[T]]

    def observe(observer: Observer[T]): Cancellable = {
      subscribers += observer
      Cancellable(subscribers -= observer)
    }
    
    def onNext(next: T) = {      
      subscribers.foreach(_.onNext(next))      
    }
    
    def onError(e: Throwable) = {
      subscribers.foreach(_.onError(e))
      subscribers.clear()
    }
    
    def onCompleted() = {
      subscribers.foreach(_.onCompleted())
      subscribers.clear()
    }
  }
}