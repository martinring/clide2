package clide.client.ui.html

import scalajs.js
import clide.client.rx._
import clide.client.util.Cancellable

trait Readable[T,-E <: Control] { 
  def read(target: Any): T
  
  def --[E2 <: E](events: Event[_,E2]*) = new EventReadable[T,E] {
    def --> (obs: Observer[T]) = BoundAttribute[T,E] { t =>      
      val es = events.map(_.attach(t, Observer(_ => obs.onNext(read(t)))))
      Cancellable(es.map(_.cancel()))
    }
  }
  
  def map[U](f: T => U) = Readable[U,E](t => f(read(t)))
}

object Readable {
  def apply[T,E <: Control](r: Any => T) = new Readable[T,E] {
    def read(target: Any): T = r(target)
  } 
}

trait EventReadable[T,-E <: Control] {
  def --> (obs: Observer[T]): BoundAttribute[T,E]
}

trait Writable[T,-E <: Control] { 
  def write(target: Any, value: T): Unit
  
  def := (value: T) = BoundAttribute[T,E]{ t => 
    write(t,value)
    Cancellable() 
  }
  
  def <-- (obs: Observable[T]) = BoundAttribute[T,E]{ t => 
    obs.observe(write(t,_)) 
  }
}

object Attribute {
  def apply[T,E <: Control](name: String) = new Readable[T,E] with Writable[T,E] {
    def read(target: Any): T = target.asInstanceOf[js.Dynamic].selectDynamic(name).asInstanceOf[T]
    def write(target: Any, value: T): Unit = target.asInstanceOf[js.Dynamic].updateDynamic(name)(value.asInstanceOf[js.Dynamic])
  }
  
  def writeable[T,E <: Control](name: String) = new Writable[T,E] {
    def write(target: Any, value: T): Unit = target.asInstanceOf[js.Dynamic].updateDynamic(name)(value.asInstanceOf[js.Dynamic])
  }
  
  def readable[T,E <: Control](name: String) = new Readable[T,E] { 
    def read(target: Any): T = target.asInstanceOf[js.Dynamic].selectDynamic(name).asInstanceOf[T]
  }
}

trait BoundAttribute[T, -E <: Control] {
  def attach(target: Any): Cancellable  
}

object BoundAttribute {
  def apply[T,E <: Control](a: Any => Cancellable) = new BoundAttribute[T,E] {
    def attach(target: Any) = a(target)
  }
}