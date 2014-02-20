package clide.reactive

import scala.util.Try
import scala.util.Success
import scala.util.Failure
import scala.concurrent.Future
import scala.concurrent.ExecutionContext

case class Evt[A](next: Future[Option[(A,Evt[A])]]) {  
  def map[B](f: A => B)(implicit executionContext: ExecutionContext): Evt[B] = 
    Evt(next.map(_.map(x => (f(x._1),x._2.map(f)))))
  def merge(that: Evt[A]) = Future.firstCompletedOf(Seq(this.next,that.next))
}

trait Event[+A] {  
  def fold[B](start: B)(f: (B,A) => B): Future[B]
    
  def map[B](f: A => B) = Event[B] { r =>
    feed(Reactive.stateful(r)((r, a) => r.react(a.map(_.map(f)))))
  }

  def scan[B](start: B)(f: (B,A) => B) = Event[B] { r =>
    feed(Reactive.stateful((Success(Some(start)): Try[Option[B]],r)) {
      case ((b,state), a) =>
        val r = for { b <- b; a <- a } yield 
                for { b <- b; a <- a } yield f (b,a)
        (r,state.react(r))        
    })
  }
  
  def merge(that: Event[A]) = Event[A] { r =>
    this.feed(Reactive.stateful(r)((r,a) => r.react(a))) andThen
    that.feed(Reactive.stateful(r)((r,a) => r.react(a)))    
  }
  
  def sample[B](target: Continuous[B]): Event[B] = map(_ => target.now)
}

object Event {
  def apply[A](f: Reactive[A] => Disposable): Event[A] = new Event[A] {
    def feed(r: Reactive[A]): Disposable = f(r)
  }
}