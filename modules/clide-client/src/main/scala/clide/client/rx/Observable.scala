package clide.client.rx

import scalajs.js
import scala.util.Try
import scala.util.Success
import scala.util.Failure
import org.scalajs.dom._
import clide.client.util.Cancellable
import clide.client.util.Buffer

trait Observable[+T] {  
  def observe(observer: Observer[T]): Cancellable
  
  def observe(onNext: T => Unit = _ => (), onError: Throwable => Unit = _ => (), onCompleted: () => Unit = () => ()): Cancellable =
    observe(Observer(onNext,onError,onCompleted))
    
  def foreach(f: T => Unit): Cancellable = observe(Observer(f))  
  
  def filter(p: T => Boolean) = Observable { (obs: Observer[T]) =>
    observe(
      (t: T) => Try(p(t)) match { 
        case Success(b) => if (b) obs.onNext(t) 
        case Failure(e) => obs.onError(e) 
      },
      obs.onError, obs.onCompleted
    )
  }
  
  def startWith[U >: T](getter: => U) = Observable {    
    (obs: Observer[U]) =>
      Try(getter) match {
        case Success(v) => 
          obs.onNext(v)
          observe(obs)
        case Failure(e) => 
          obs.onError(e)
          Cancellable()
      }
  }
  
  def varying = Observable {    
    (obs: Observer[T]) => 
      var cache: Option[T] = None
      observe(
        (t: T) => if (!cache.exists(_ == t)) {
          cache = Some(t)
          obs.onNext(t)
        },
        obs.onError, obs.onCompleted
      )
  }
  
  def map[U](f: T => U) = Observable { (obs: Observer[U]) =>
    observe(
      (t: T) => Try(f(t)) match { 
        case Success(v) => obs.onNext(v) 
        case Failure(e) => obs.onError(e) 
      },
      obs.onError, obs.onCompleted
    )
  }
    
  def flatMap[U](f: T => Observable[U]) = Observable { (obs: Observer[U]) =>
    val subscriptions = Buffer.empty[Cancellable]
    val main = observe(
      (t: T) => Try(f(t)) match {
        case Success(o) => subscriptions += o.observe(obs)
        case Failure(e) => obs.onError(e)
      }, obs.onError, obs.onCompleted
    )
    Cancellable{
      main.cancel(); 
      subscriptions.foreach(_.cancel())
    }
  }
  
  def zip[U](other: Observable[U]) = Observable { (obs: Observer[(T,U)]) =>
    val left: Buffer[T] = Buffer.empty
    val right: Buffer[U] = Buffer.empty    
    lazy val s1: Cancellable = observe(
      (t: T) => if (right.nonEmpty && left.isEmpty) obs.onNext (t, right.removeHead)
              else left += t,
      obs.onError, () => { obs.onCompleted(); s2.cancel() } // TODO: Cancel other      
    )
    lazy val s2: Cancellable = other.observe(
      (u: U) => if (left.nonEmpty && right.isEmpty) obs.onNext (left.removeHead, u)
              else right += u,
      obs.onError, () => { obs.onCompleted(); s1.cancel() }
    )
    (s1,s2)
    Cancellable {
      s1.cancel()
      s2.cancel()
    }
  }
  
  def zipWithIndex: Observable[(T, Int)] = {
    var n = 0;
    this.map(x => { val result = (x,n); n += 1; result })
  }
  
  def take(n: Int) = Observable { (obs: Observer[T]) =>
    var c = 0
    lazy val s1: Cancellable = observe(
      (t: T) => if (n > c) { 
        obs.onNext(t) 
        c += 1 
      } else {
        s1.cancel()
        obs.onCompleted()
      },
      obs.onError, obs.onCompleted
    )
    s1
  }
  
  def drop(n: Int) = Observable { (obs: Observer[T]) =>
    var c = 0
    observe(
      (t: T) => if (n <= c) { 
        obs.onNext(t) 
        c += 1 
      },
      obs.onError, obs.onCompleted
    )
  }  
  
  def head: Observable[T] = take(1)
  
  def tail: Observable[T] = drop(1)
}

object Observable {
  def apply[T](f: Observer[T] => Cancellable): Observable[T] = new Observable[T] {
    def observe(observer: Observer[T]) = f(observer)
  }
  
  def from[T](buf: Buffer[T]): Observable[T] = Observable{ obs => 
    buf.foreach(obs.onNext(_))
    Cancellable()
  }
  
  def from[T](t: T): Observable[T] = Observable { obs =>
    obs.onNext(t)
    Cancellable()
  }
  
  def interval(delay: Int): Observable[Long] = new Observable[Long] {
    def observe(observer: Observer[Long]) = {
      var counter = 0L
      var interval = window.setInterval(() => {
        observer.onNext(counter)
        counter += 1;
      }, delay)
      Cancellable(window.clearInterval(interval))
    }
  }
  
  def fromEvent[T](obj: EventTarget, event: String) = {    
    new Observable[T] {
      def observe(observer: Observer[T]) = {
        val listener: scala.scalajs.js.Function1[Event,Unit] = {(e: Event) =>
          observer.onNext(e.asInstanceOf[T])
        }
        obj.addEventListener(event, listener)
        Cancellable(obj.removeEventListener(event, listener))
      }
    }
  }
}