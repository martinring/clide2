package clide.reactive.ui.directives

import scala.concurrent.ExecutionContext
import clide.reactive.ui.Bindable
import org.scalajs.dom._
import org.scalajs.dom.raw.HTMLInputElement


trait Bindings {
  object bind {
    def checked(elem: HTMLInputElement, v: Bindable[Boolean])(implicit ec: ExecutionContext) = {
      elem.checked = v.get
      v.watch.foreach(elem.checked = _)
      elem.addEventListener("change", (e: Event) => v := elem.checked)      
    }
    
    def value(elem: HTMLInputElement, v: Bindable[String])(implicit ec: ExecutionContext) = {
      elem.value = v.get
      v.watch.foreach(elem.value = _)
      elem.addEventListener("input", (e: Event) => if (elem.validity.valid) v := elem.value)
    }
  }
}