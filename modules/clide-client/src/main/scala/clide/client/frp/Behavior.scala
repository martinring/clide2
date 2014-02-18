package clide.client.frp

trait UserAction
case object MouseClick extends UserAction

case class Time(val millis: Long) extends AnyVal

case class Behavior[A](val f: (Stream[Option[UserAction]],Stream[Time]) => Stream[A]) extends AnyVal {
  def until(e: Event[Behavior[A]]): Behavior[A] = {
    def loop(us: Stream[Option[UserAction]], ts: Stream[Time], es: Stream[Option[Behavior[A]]], bs: Stream[A]): Stream[A] = {
      (us,ts,es,bs) match {
        case (_ #:: us, _ #:: ts, e #:: es, b #:: bs) => b #:: (e match {
          case None => loop(us,ts,es,bs)
          case Some(Behavior(fb)) => fb(us,ts)
        })
      }
    }
    Behavior { (us,ts) =>
      loop(us,ts,e.f(us,ts),f(us,ts))
    }
  }
  
  def switch(e: Event[Behavior[A]]): Behavior[A] = {
    def loop(us: Stream[Option[UserAction]], ts: Stream[Time], es: Stream[Option[Behavior[A]]], bs: Stream[A]): Stream[A] = {
      (us,ts,es,bs) match {
        case (_ #:: us, _ #:: ts, e #:: es, b #:: bs) => b #:: (e match {
          case None => loop(us,ts,es,bs)
          case Some(Behavior(fb)) => loop(us,ts,es,fb(us,ts))
        })
      }
    }
    Behavior { (us,ts) =>
      loop(us,ts,e.f(us,ts),f(us,ts))
    }
  }    
}

object Behavior {
  def time: Behavior[Time] = Behavior { (_,t) => t }
  def const[A](x: A): Behavior[A] = Behavior { (_,_) => Stream.continually(x) }  
}

case class Event[A](val f: (Stream[Option[UserAction]],Stream[Time]) => Stream[Option[A]]) extends AnyVal {
  def unique = {
    def aux(xs: Stream[Option[A]]): Stream[Option[A]] = 
      xs.zip(None #:: xs).map{ case (x,y) => if (x == y) None else y }
    Event { (u,t) => aux(f(u,t)) }
  }
  
  def =>>[B](g: A => B): Event[B] = Event { (u,t) => f(u,t).map(_.map(g)) }
  
  def ->>[B](b: B): Event[B] = this =>> (_ => b) 
}

object Event {
  def `while`(b: Behavior[Boolean]): Event[Unit] = Event { (us,ts) => b.f(us,ts).map(b => if (b) Some () else None) }
  def when(b: Behavior[Boolean]): Event[Unit] = `while`(b).unique
  def step[A](a: A, e: Event[A]): Behavior[A] = Behavior.const(a) switch e =>> (Behavior.const)
  def mouseClicks = Event { (uas,_) => uas.map(_.flatMap { case MouseClick => Some (); case _ => None }) }
}