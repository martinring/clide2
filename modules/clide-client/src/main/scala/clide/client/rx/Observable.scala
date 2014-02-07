package clide.client.rx

import scalajs.js
import scala.scalajs.js.Any.fromFunction1
import scala.scalajs.js.Any.fromString
import scala.util.Try
import scala.util.Success
import scala.util.Failure
import scala.concurrent.duration.Duration

trait Observable[+T] {  
  def subscribe(observer: Observer[T]): Subscription
  
  def +=(f: T => Unit): Subscription = subscribe(Observer(f,(e) => (), () => println("onComplete")))
  
  def foreach(f: T => Unit) {
    subscribe(Observer(f))
  }
  
  def filter(p: T => Boolean) = {
    val s = subscribe _
    new Observable[T] {
      def subscribe(obs: Observer[T]) = s(Observer(
          onNext = { (t: T) =>
            Try(p(t)) match {
              case Success(b) => if (b) obs.onNext(t)
              case Failure(e) => obs.onError(e)
            }
          },
          onError = obs.onError,
          onCompleted = obs.onCompleted
      ))
    }
  }
  
  /*def take(n: Int) = {
    val s = subscribe _
    new Observable[T] {      
      def subscribe(obs: Observer[T]) = {
        var count = 0
        if (n == count) {
          obs.onCompleted()
          Subscription()
        }
        else {
          s(Observer(onNext = { (t: T) =>
            obs.onNext(t)
            count += 1
            if (n == count) {
              obs.onCompleted()
            } else {
              obs.onNext(t)
            }
          }))
        }
      }
        
    }
  }*/
  
  def map[U](f: T => U) = {
    val s = subscribe _
    new Observable[U] {
      def subscribe(obs: Observer[U]) = s(Observer(
          onNext = { (t: T) =>
            Try(f(t)) match {
              case Success(v) => obs.onNext(v)
              case Failure(e) => obs.onError(e)
            }            
          },
          onError     = obs.onError,
          onCompleted = obs.onCompleted
      ))
    }   
  }
    
  def flatMap[U](f: T => Observable[U]) = {
    val s = subscribe _
    new Observable[U] {
      def subscribe(obs: Observer[U]) = {
        var subscriptions = List.empty[Subscription]
        val subscr = s(Observer(
          onNext = { (t: T) =>
            Try(f(t)) match {
              case Success(o) => 
                subscriptions ::= o.subscribe(obs)
              case Failure(e) => obs.onError(e)
            }
          },
          onError = obs.onError,
          onCompleted = obs.onCompleted
        ))
        Subscription{
          subscriptions.foreach(_.unsubscribe)
          subscr.unsubscribe()
        }
      }
    }
  }
  
  def zip[U](other: Observable[U]) = {
    val s = subscribe _
    new Observable[(T,U)] {
      def subscribe(obs: Observer[(T,U)]) = {
        var latestT: Option[T] = None
        var latestU: Option[U] = None

        val s1: Subscription = s(Observer(onNext = { t =>
          latestT = Some(t)
          (latestT,latestU) match {
            case (Some(t),Some(u)) => (t,u)
            case _ =>
          } 
        },obs.onError, obs.onCompleted))
        
        val s2: Subscription = other.subscribe(Observer(onNext = { u =>
          latestU = Some(u)
          (latestT,latestU) match {
            case (Some(t),Some(u)) => (t,u)
            case _ =>
          }
        },obs.onError, obs.onCompleted))

        Subscription{s1.unsubscribe; s2.unsubscribe}
      }
    }
  }
  
  def throttle(delay: Double) = {
    val s = subscribe _
    new Observable[T] {
      def subscribe(obs: Observer[T]) = {
        var latest: Option[T] = None
        var timeout: Option[js.Number] = None
                  
        def f(): Unit = {
          latest match {
            case Some(v) =>
              latest = None
              obs.onNext(v)
              timeout = Some(window.setTimeout(() => f(), delay))
            case None =>
              timeout = None
          }                                        
        }
        
        val underlying = s(Observer.apply(
          onNext = { (t: T) =>
            if (timeout.isDefined) {
              latest = Some(t)
            } else {
              obs.onNext(t)
              timeout = Some(window.setTimeout(() => f(), delay))
            }
          },
          onError = obs.onError, 
          onCompleted = obs.onCompleted))
          
        Subscription{
          timeout.foreach(window.clearTimeout)
          underlying.unsubscribe
        }
      }
        
    }
  }
}

object Observable {
  /*def interval(delay: Int): Observable[Long] = new Observable[Long] {
    def subscribe(observer: Observer[Long]) = {
      var counter = 0L
      var interval = window.setInterval(() => {
        observer.onNext(counter)
        counter += 1;
      }, delay)
      Subscription(window.clearInterval(interval))
    }
  }
  
  def fromEvent[T](obj: EventTarget, event: String) = {    
    new Observable[T] {
      def subscribe(observer: Observer[T]) = {
        val listener: scala.scalajs.js.Function1[Event,Unit] = {(e: Event) =>
          observer.onNext(e.asInstanceOf[T])
        }
        obj.addEventListener(event, listener)
        Subscription.apply(obj.removeEventListener(event, listener))
      }
    }
  }
  */
}