package clide.reactive

trait Event[+A] {  
  def feed(reactive: Reactive[A]): Event[A]
  
  def map[B](f: A => B) = Event[B] { r => 
    feed(Reactive.scanner(r)((r,a) => r.step(f(a))))
  }
}

object Event {
  def apply[A](f: Reactive[A] => Event[A]): Event[A] = new Event[A] {
    def feed(r: Reactive[A]): Event[A] = f(r)
  }
}