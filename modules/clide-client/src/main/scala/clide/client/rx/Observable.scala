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
  
  def observe(onNext: T => Unit = _ => (), onError: Throwable => Unit = e => throw e, onCompleted: () => Unit = () => ()): Cancellable =
    observe(Observer(onNext,onError,onCompleted))
  
  def materialize = Observable[Step[T]] { obs =>
    observe(
      (t: T) => obs.onNext(Next(t)),
      (e: Throwable) => obs.onNext(Error(e)),
      () => obs.onNext(Completed)
    )
  }
    
  def foreach(f: T => Unit): Cancellable = observe(Observer(f))  
  
  def filter(p: T => Boolean) = Observable[T] { obs =>
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
  
  def collect[U](f: PartialFunction[T,U]) = Observable { (obs: Observer[U]) =>
    observe(
      (t: T) => Try(f.lift(t)) match {
        case Success(Some(v)) => obs.onNext(v)
        case Success(None) => // skip value
        case Failure(e) => obs.onError(e)
      }
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
  
  def until[U](that: Observable[U]) = Observable[T] { obs =>
    val s = this.observe(obs)
    lazy val s2: Cancellable = that.observe(
        _ => { obs.onCompleted(); s.cancel(); s2.cancel() }, 
        e => { obs.onError(e); s.cancel(); s2.cancel() }, 
        () => { obs.onCompleted(); s.cancel(); s2.cancel() })
    s and s2
  }
  
  def ended = Observable[Unit] { obs =>    
    observe(_ => (), obs.onError, () => { obs.onNext(()); obs.onCompleted() })
  }
  
  def merge[U >: T](that: Observable[U]) = Observable[U] { obs => 
    this.until(that.ended).observe(obs) and
    that.until(this.ended).observe(obs)
  }
  
  def when(that: Observable[Boolean]) = Observable[T] { obs =>
    var s = Option.empty[Cancellable]    
    that.until(that.ended).observe({b => 
      if (b && s.isEmpty) s = Some(observe(obs)) 
      else if (!b) { 
        s.foreach(_.cancel()); 
        s = None 
    }}, { e =>
      s.foreach(_.cancel())
      obs.onError(e)
    } , { () =>
      s.foreach(_.cancel())
      obs.onCompleted()
    })
  }
  
  def zip[U](that: Observable[U]) = Observable { (obs: Observer[(T,U)]) =>
    val left: Buffer[T] = Buffer.empty
    val right: Buffer[U] = Buffer.empty    
    this.until(that.ended).observe(
      (t: T) => if (right.nonEmpty && left.isEmpty) obs.onNext (t, right.remove(0))
                else left += t,
      obs.onError, obs.onCompleted      
    ) and
    that.until(this.ended).observe(
      (u: U) => if (left.nonEmpty && right.isEmpty) obs.onNext (left.remove(0), u)
                else right += u,
      obs.onError, obs.onCompleted
    )
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
  
  /**
   * Flip-flopping observable. Turns true whenever an event in flip occurs and false whenever 
   * an event in flop occurs. Ends when either flip or flop ends
   */
  def flipFlop[T,U](flip: Observable[T], flop: Observable[U]) =
    (flip.map(_ => true) merge flop.map(_ => false)).varying
  
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
          //e.preventDefault()
          observer.onNext(e.asInstanceOf[T])
        }
        obj.addEventListener(event, listener)
        Cancellable(obj.removeEventListener(event, listener))
      }
    }
  }
}