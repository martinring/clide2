package clide.client.ui.html

import scalajs.js
import clide.client.rx._
import clide.client.util.Cancellable
import org.scalajs.dom.HTMLElement

trait Readable[T,E <: Control] { 
  def read(target: HTMLElement): T
  
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
  def apply[T,E <: Control](r: HTMLElement => T) = new Readable[T,E] {
    def read(target: HTMLElement): T = r(target)
  } 
}

trait EventReadable[T,E <: Control] {
  def --> (obs: Observer[T]): BoundAttribute[E]
}

trait Writable[T,E <: Control] { 
  def write(target: HTMLElement, value: T): Unit
  
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
    if (v.getter.isDefined)
      sys.error("getter is already bound")
    if (v.setter.isDefined)
      sys.error("setter is already bound")
    v.getter = Some(() => read(t))
    v.setter = Some(v => write(t,v))
    Cancellable {
      v.update()
      v.getter = None
      v.setter = None
    }
  }
}

trait AttributeValueMapper[T] {
  def read(value: String): T
  def write(value: T): String
}

object AttributeValueMapper {
  def apply[T](r: String => T, w: T => String) = new AttributeValueMapper[T] {
    def read(value: String) = r(value)
    def write(value: T) = w(value)
  }
  
  implicit val stringMapper = AttributeValueMapper[String](identity,identity)
}

object Attribute {
  private def writeNamed[T](target: HTMLElement, value: T, name: String)(implicit mapper: AttributeValueMapper[T]) =
    target.asInstanceOf[js.Dynamic].updateDynamic(name)(mapper.write(value))    
    
  private def readNamed[T](target: HTMLElement, name: String)(implicit mapper: AttributeValueMapper[T]) =
    mapper.read(target.asInstanceOf[js.Dynamic].selectDynamic(name).asInstanceOf[js.String])
    
  def apply[T,E <: Control](name: String)(implicit mapper: AttributeValueMapper[T]) = new ReadAndWritable[T,E] {
    def read(target: HTMLElement): T = readNamed(target,name)
    def write(target: HTMLElement, value: T): Unit = writeNamed(target,value,name)
  }
  
  def writeable[T,E <: Control](name: String)(implicit mapper: AttributeValueMapper[T]) = new Writable[T,E] {
    def write(target: HTMLElement, value: T): Unit = writeNamed(target,value,name)
  }
  
  def readable[T,E <: Control](name: String)(implicit mapper: AttributeValueMapper[T]) = new Readable[T,E] { 
    def read(target: HTMLElement): T = readNamed(target,name)
  }
  
  def flag[E <: Control](name: String) = new ReadAndWritable[Boolean,E] {
    def read(target: HTMLElement): Boolean = target.getAttribute(name) == name.asInstanceOf[js.String]
    def write(target: HTMLElement, value: Boolean) = if (!value) target.removeAttribute(name) else target.setAttribute(name,name)
  }  
}

trait BoundAttribute[-E <: Control] {
  def attach(target: HTMLElement): Cancellable  
}

object BoundAttribute {
  def apply[E <: Control](a: HTMLElement => Cancellable) = new BoundAttribute[E] {
    def attach(target: HTMLElement) = a(target)
  }
}