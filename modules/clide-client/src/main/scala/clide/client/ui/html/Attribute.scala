package clide.client.ui.html

import scalajs.js
import clide.client.rx._
import clide.client.util.Cancellable
import org.scalajs.dom.HTMLElement

trait Readable[T,E <: Control] { 
  def read(target: Any): T
  
  def --(events: Event[_,E]*) = new EventReadable[T,E] {
    def --> (obs: Observer[T]) = BoundAttribute[E] { t =>      
      val es = events.map(_.attach(t).observe(_ => obs.onNext(read(t))))
      Cancellable(es.map(_.cancel()))
    }
  }
  
  def -->(v: Var[T]) = BoundAttribute[E] { t => 
    v.getter = Some(() => read(t))
    Cancellable(v.getter = None)
  }
  
  def map[U](f: T => U) = Readable[U,E](t => f(read(t)))
}

object Readable {
  def apply[T,E <: Control](r: Any => T) = new Readable[T,E] {
    def read(target: Any): T = r(target)
  } 
}

trait EventReadable[T,E <: Control] {
  def --> (obs: Observer[T]): BoundAttribute[E]
}

trait Writable[T,E <: Control] { 
  def write(target: Any, value: T): Unit
  
  def := (value: T) = BoundAttribute[E]{ t => 
    write(t,value)
    Cancellable() 
  }
  
  def <-- (obs: Observable[T]) = BoundAttribute[E]{ t => 
    obs.observe(write(t,_)) 
  }
}

trait ReadAndWritable[T,E <: Control] extends Readable[T,E] with Writable[T,E] { 
  def <-> (v: Var[T]) = BoundAttribute[E] { t =>
    write(t,v.get)
    v.getter = Some(() => read(t))
    v.setter = Some(v => write(t,v))    
    Cancellable {
      v.getter = None
      v.setter = None
    }
  }
}

object Attribute {
  private def writeNamed[T](target: Any, value: T, name: String) =
    target.asInstanceOf[js.Dynamic].updateDynamic(name)(value.asInstanceOf[js.Dynamic])
    
  private def readNamed[T](target: Any, name: String) =
    target.asInstanceOf[js.Dynamic].selectDynamic(name).asInstanceOf[T]
    
  def apply[T,E <: Control](name: String) = new ReadAndWritable[T,E] {
    def read(target: Any): T = readNamed(target,name)
    def write(target: Any, value: T): Unit = writeNamed(target,value,name)
  }
  
  def writeable[T,E <: Control](name: String) = new Writable[T,E] {
    def write(target: Any, value: T): Unit = writeNamed(target,value,name)
  }
  
  def readable[T,E <: Control](name: String) = new Readable[T,E] { 
    def read(target: Any): T = readNamed(target,name)        
  }
  
  def flag[E <: Control](name: String) = new ReadAndWritable[Boolean,E] {
    def read(target: Any): Boolean = readNamed(target,name)
    def write(target: Any, value: Boolean) = if (!value) target.asInstanceOf[HTMLElement].removeAttribute(name) else target.asInstanceOf[js.Dynamic].updateDynamic(name)(name)
  }
}

trait BoundAttribute[-E <: Control] {
  def attach(target: Any): Cancellable  
}

object BoundAttribute {
  def apply[E <: Control](a: Any => Cancellable) = new BoundAttribute[E] {
    def attach(target: Any) = a(target)
  }
}