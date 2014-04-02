package clide.reactive

import scala.concurrent.Future
import scala.concurrent.ExecutionContext
import scala.concurrent.Promise
import scala.util.Try
import scala.util.Success
import scala.util.Failure
import scala.concurrent.duration.Duration
import scala.math.Numeric
import scala.concurrent.duration.FiniteDuration

/**
 * An Event is an asynchronous List:
 * 
 * Type List has the two Constructors `Nil` and `::[A](A,List[A])`. This could be 
 * represented as `type List[A] = Option[(A,List[A])]` where `Nil = None` and
 *  `:: = Some`.
 * 
 * An Event makes the List asynchronous by wrapping every value in a Future:
 * 
 *     Event[A] = Future[Option[(A,Event[A])]]
 *     
 * This means that while Events support the same kinds of operations as Lists
 * (e.g. `map`, `flatMap`, `filter`, etc.), there are semantic differences which
 * make them incompatible with other collection types:
 * 
 *  * Results of operations that return a single value are wrapped in a `Future`:
 *    e.g. `length` returns a Future[Long] or `foldLeft` return  
 * 
 */
trait Event[+A] {
  private[reactive] def next: Future[Option[(A,Event[A])]]
  private[reactive] def stop(): Unit
  private[reactive] def isCompleted: Boolean = next.isCompleted
  
  protected def stopWith(f: => Unit)(implicit ec: ExecutionContext): Event[A] = 
    Event(next.map {
      case None => None
      case Some((a,e)) => Some((a,e.stopWith(f)))
    })(f)
    
  def duplicate(implicit ec: ExecutionContext): (Event[A], Event[A]) = {
    val leftC = Promise[Unit]
    val rightC = Promise[Unit]
    leftC.future.onComplete(_ => rightC.future.onComplete(_ => stop()))
    (this.stopWith(leftC.success()),this.stopWith(rightC.success()))
  }
      
  def map[B](f: A => B)(implicit ec: ExecutionContext): Event[B] =  
    Event(next.map {  
      case None => None
      case Some((a,e)) => Some((f(a),e.map(f)))
    })(stop())        
    
  def mapF[B](f: A => Future[B])(implicit ec: ExecutionContext): Event[B] =
    Event(next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) => f(a).map(b => Some(b,e.mapF(f)))
    })(stop())
       
  def flatMap[B](f: A => Event[B])(implicit ec: ExecutionContext): Event[B] =
    Event(next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) =>         
        (f(a) merge e.flatMap(f)).next
    })(stop())
  
  def filter(f: A => Boolean)(implicit ec: ExecutionContext): Event[A] = 
    Event(next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) if f(a) => Future.successful(Some(a,e.filter(f)))
      case Some((a,e))         => Event(e.next)(e.stop()).filter(f).next
    })(stop())
        
  def withFilter(f: A => Boolean)(implicit ec: ExecutionContext): Event[A] =
    filter(f)
    
  def partition(f: A => Boolean)(implicit ec: ExecutionContext): (Event[A],Event[A]) =
    duplicate match { case (l,r) => (l filter f, r filter (!f(_))) }
    
  def timeSpan(f: Future[_])(implicit ec: ExecutionContext): (Event[A],Event[A]) =
    duplicate match { case (l,r) => (l until f, r dropUntil f) }
    
  def collect[B](f: PartialFunction[A,B])(implicit ec: ExecutionContext): Event[B] =
    this.filter(f.isDefinedAt).map(f)
  
  def take(n: Int)(implicit ec: ExecutionContext): Event[A] =     
    Event(
      if (n <= 0) { this.stop(); Future.successful(None) }
      else next.map {
        case None => None
        case Some((a,e)) => Some(a,e.take(n-1))
      })(stop())
  
  def takeWhile(p: A => Boolean)(implicit ec: ExecutionContext): Event[A] = 
    Event(next.map {
      case None => None
      case Some((a,e)) => if (p(a)) Some((a,e.takeWhile(p))) else { e.stop; None }
    })(stop())
        
  def drop(n: Int)(implicit ec: ExecutionContext): Event[A] = 
    if (n <= 0) this
    else Event(next.flatMap {
      case None => Future.successful(None)
      case Some((_,e)) => e.drop(n - 1).next
    })(stop())
  
  def dropWhile(p: A => Boolean)(implicit ec: ExecutionContext): Event[A] =
    Event(next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) => if (p(a)) e.dropWhile(p).next else Future.successful(Some((a,e)))
    })(stop())
  
  def headOption(implicit ec: ExecutionContext): Future[Option[A]] = 
    next.map{x => stop(); x.map(_._1)}
    
  def head(implicit ec: ExecutionContext): Future[A] =
    headOption.map(_.getOrElse(throw new NoSuchElementException("Event.head on empty event")))     
  
  def lastOption(implicit ec: ExecutionContext): Future[Option[A]] =
    foldLeft(Option.empty[A])((_,a) => Some(a))

  def last(implicit ec: ExecutionContext): Future[A] =
    lastOption.map(_.getOrElse(throw new NoSuchElementException("Event.last on empty event")))
    
  def tail(implicit ec: ExecutionContext): Future[Event[A]] = next.map {
    case None => throw new UnsupportedOperationException("Event.tail on empty event")
    case Some((_,tail)) => tail
  }

  def apply(index: Int)(implicit ec: ExecutionContext): Future[A] = 
    if (index < 0) Future.failed(new IndexOutOfBoundsException)
    else if (index == 0) head
    else next.flatMap {
      case None => throw new IndexOutOfBoundsException
      case Some((_,e)) => e(index - 1)
    }
  
  def zipWith[B, AB](that: Event[B], f: (A,B) => AB)(implicit ec: ExecutionContext): Event[AB] = Event {
    for {
      x <- this.next
      y <- that.next
    } yield (x,y) match {
      case (Some((a,ae)),Some((b,be))) => Some((f(a,b),ae.zipWith(be, f)))
      case (Some((_,e)),None) => e.stop(); None
      case (None,Some((_,e))) => e.stop(); None
      case (None,None) => None
    }
  } { this.stop(); that.stop() }
  
  def zip[B](that: Event[B])(implicit ec: ExecutionContext): Event[(A,B)] =
    zipWith(that, (a: A, b: B) => (a,b))
    
  def zipWithIndex(implicit ec: ExecutionContext): Event[(A,Long)] =
    duplicate match { case (l,r) => l zip r.indices }
  
  def merge[B >: A](that: Event[B])(implicit ec: ExecutionContext): Event[B] = Event {
    Future.firstCompletedOf(Traversable(this.next, that.next)).flatMap { _ =>
      if (this.next.isCompleted) this.next.flatMap {
        case None => that.next
        case Some((a,e)) => Future.successful(Some((a,e merge that)))
      } else that.next.flatMap {
        case None => this.next
        case Some((b,e)) => Future.successful(Some((b,this merge e)))
      }
    }
  } { this.stop(); that.stop() }   

  def ++[B >: A](that: Event[B])(implicit ec: ExecutionContext): Event[B] = Event {
    next.flatMap {
      case None => that.next
      case Some((a,e)) => Future.successful(Some(a,e ++ that))
    }
  } { this.stop(); that.stop() }

  def :+[B >: A](elem: B)(implicit ec: ExecutionContext): Event[B] = 
    this ++ Event.single(elem)
  
  def +:[B >: A](elem: B)(implicit ec: ExecutionContext): Event[B] = 
    Event(Future.successful(Some(elem,this)))(this.stop())
    
  def +[B >: A](elem: Future[B])(implicit ec: ExecutionContext): Event[B] = 
    merge(Event.single(elem))    
  
  def find(f: A => Boolean)(implicit ec: ExecutionContext): Future[Option[A]] =
    next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) => if (f(a)) { e.stop(); Future.successful(Some(a)) } else e.find(f)
    }
  
  def completedSpan: (List[A],Event[A]) =
    next.value match {
      case None => (Nil, this)
      case Some(result) =>
        result.get match {
          case None => (Nil, this)
          case Some((head,e)) => 
            val (tail,rest) = e.completedSpan
            (head :: tail, rest)
        }
    }    
  
  def dropUntil(resume: Future[_])(implicit ec: ExecutionContext): Event[A] = 
    Event(resume.flatMap(_ => this.completedSpan._2.next))(stop)
  
  def exists(f: A => Boolean)(implicit ec: ExecutionContext): Future[Boolean] =
    find(f).map(_.isDefined)
    
  def forall(f: A => Boolean)(implicit ec: ExecutionContext): Future[Boolean] =
    find(!f(_)).map(_.isEmpty)
    
  def contains(elem: Any)(implicit ec: ExecutionContext): Future[Boolean] = 
    exists(_ == elem)
  
  def count(p: A => Boolean)(implicit ec: ExecutionContext): Future[Long] = 
    foldLeft(0L)((n,e) => if (p(e)) n + 1 else n)
          
  def indices(implicit ec: ExecutionContext): Event[Long] =
    scan(-1L)((n,_) => n+1)
    
  def length(implicit ec: ExecutionContext): Future[Long] =
    foldLeft(0L)((n,_) => n+1)
    
  def length_>=(n: Int)(implicit ec: ExecutionContext): Future[Boolean] =
    indices.exists(_ >= n)
    
  def length_>(n: Int)(implicit ec: ExecutionContext): Future[Boolean] =
    indices.exists(_ > n)
    
  def foldLeft[B](start: B)(f: (B,A) => B)(implicit ec: ExecutionContext): Future[B] =
    next.flatMap {
      case None => Future.successful(start)
      case Some((a,e)) => e.foldLeft(f(start,a))(f)
    }   
    
  def scan[B](start: B)(f: (B,A) => B)(implicit ec: ExecutionContext): Event[B] = 
    Event(next.map {
      case None => None
      case Some((a,e)) =>
        val b = f(start,a)
        Some(b,e.scan(b)(f))
    })(stop())
  
  def scanF[B](start: B)(f: (B,A) => Future[B])(implicit ec: ExecutionContext): Event[B] =
    Event(next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) =>
        f(start,a).map(b => Some(b,e.scanF(b)(f)))
    })(stop())

  def switch[B](implicit ec: ExecutionContext, evidence: Event[A] <:< Event[Event[B]]): Event[B] =    
    Event(evidence(this).next.flatMap {
      case None => Future.successful(None)
      case Some((a,e)) => (a.until(e.next) ++ e.switch).next
    })(stop())
  
  def until[B](done: Future[B])(implicit ec: ExecutionContext): Event[A] =
    Event(Future.firstCompletedOf(Seq(done,next)).map { _ =>
      if (done.isCompleted) { stop(); None }
      else next.value.get.get match {
        case None => None
        case Some((a,e)) => Some((a,e.until(done)))
      }})(stop())

  def span(f: A => Boolean)(implicit ec: ExecutionContext): (Event[A],Event[A]) =
    duplicate match { case (l,r) => (takeWhile(f),dropWhile(f)) }
          
  def spanF(f: Future[_])(implicit ec: ExecutionContext): (Event[A],Event[A]) =
    span(_ => !f.isCompleted)
    
  def spanT(duration: FiniteDuration)(implicit ec: ExecutionContext, scheduler: Scheduler): (Event[A],Event[A]) =
    spanF(scheduler.timeout(duration))
      
  def splitBy[B](that: Event[B])(implicit ec: ExecutionContext): Event[Event[A]] = {
    val (head,tail) = timeSpan(that.head)
    head +: tail.splitBy(that)
  }
  
  def timestamped(implicit ec: ExecutionContext, scheduler: Scheduler): Event[(A,Long)] =
    zip(sample(scheduler.now))
  
  /*def window(duration: FiniteDuration)(implicit ec: ExecutionContext, scheduler: Scheduler): Event[Event[A]] =
    splitBy(Event.interval(duration))
        
  def throttle(duration: FiniteDuration)(implicit ec: ExecutionContext, scheduler: Scheduler): Event[A] =
    window(duration).mapF(_.last)*/
    
  def product[B >: A](implicit ec: ExecutionContext, num: Numeric[B]): Future[B] = 
    foldLeft(num.one)(num.times)
  
  def sum[B >: A](implicit ec: ExecutionContext, num: Numeric[B]): Future[B] =
    foldLeft(num.zero)(num.plus)
    
  //def compress(duration: FiniteDuration)(f: (A,A) => A)(implicit ec: ExecutionContext, scheduler: Scheduler): Event[A] =
  //window(duration).mapF(_.foldLeft(Option.empty[A])((r,a) => r.map(f(_,a)).getOrElse(Some(a))))
   
  def sample[B](f: => B)(implicit ec: ExecutionContext): Event[B] = map(_ => f)
  
  def foreach[U](f: A => U)(implicit ec: ExecutionContext): Future[Unit] =
    foldLeft(())((b,a) => f(a))

  def varying(implicit ec: ExecutionContext): Event[A] =
    duplicate match { case (h,t) => t.duplicate match { case (l,r) =>
      h.take(1) ++ ( l.zip(r.drop(1)).collect { case (prev,a) if a != prev => a } )
    } }
  
  def toSeq(implicit ec: ExecutionContext): Future[Seq[A]] =
    foldLeft(Seq.empty[A])((seq,a) => seq :+ a)
}

object Event {
  def apply[A](f: => Future[Option[(A,Event[A])]])(c: => Unit) = new Event[A] {
    def next = f
    def stop = {
      c
    }
  }
  
  object Completed {
    def unapply[A](event: Event[A]): Option[Option[(A,Event[A])]] = event.next.value.collect {
      case Success(x) => x
    }
  }
  
  object Failed {
    def unapply[A](event: Event[A]): Option[Throwable] = event.next.value.collect {
      case Failure(e) => e
    }
  }
  
  def empty[A] = Event[A] { Future.successful(None) } ()
  
  def interval(duration: FiniteDuration)(implicit ec: ExecutionContext, scheduler: Scheduler): Event[Long] = {
    var counter = 0L
    lazy val (event,channel) = broadcast[Long](task.cancel())
    lazy val task: Cancellable = scheduler.schedule(duration){      
      channel.push(counter)
      counter += 1
    }
    task; event
  }
  
  def single[A](value: A): Event[A] = 
    Event(Future.successful(Some(value,empty[A])))()
    
  def single[A](future: Future[A])(implicit ec: ExecutionContext): Event[A] =
    Event(future.map(value => Some(value,empty[A])))()
          
  def fromIterable[A](iterable: Iterable[A]): Event[A] = 
    iterable.foldRight(Event.empty[A])((a,b) => Event(Future.successful(Some((a,b))))())    
    
  def merge[A](es: Iterable[Event[A]])(implicit ec: ExecutionContext): Event[A] = es.size match {
    case 0 => Event.empty[A]
    case 1 => es.head
    case n => Event[A] {    
      Future.firstCompletedOf(es.map(_.next)).flatMap { _ =>
        val (completed,pending) = es.partition(_.isCompleted)
        completed.find(_.next.value.get.isFailure).map(_.next).getOrElse {
          val (values,nexts) = completed.collect {
            case Event.Completed(Some((v,n))) => (v,n)
          }.unzip
          val init = fromIterable(values)
          (init ++ merge(pending ++ nexts)).next
        }
      }
    } (es.foreach(_.stop()))
  }
  
  def flipFlop(flips: Event[_], flops: Event[_])(implicit ec: ExecutionContext): Event[Boolean] = 
    (flips.sample(true) merge flops.sample(false)).varying
  
  def broadcast[A](unsubscribe: => Unit = ())(implicit ec: ExecutionContext): (Event[A], Channel[A]) = {
    var current = Promise[Option[(A,Event[A])]]
    val head = current.future
    val channel = Channel[A](a => synchronized {
      val next = Promise[Option[(A,Event[A])]]
      if (current.isCompleted) sys.error("pushing into closed channel")
      current.completeWith(Future(Some(a,Event(next.future)(unsubscribe))))
      current = next
    })(current.failure)(current.success(None))
    (Event(head)(unsubscribe),channel)
  }
  
  def fromCallback[A](register: (A => Unit) => (() => Unit))(implicit ec: ExecutionContext): Event[A] = {
    lazy val (e,c) = broadcast[A](remove())
    lazy val remove: () => Unit = register(c.push(_))
    remove; c; return e
  }
}