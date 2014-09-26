package clide.reactive.ui

import clide.reactive._
import scala.language.implicitConversions
import scala.concurrent.ExecutionContext
import scala.reflect.ClassTag
import clide.reactive.ObservableBufferView
import scala.util.matching.Regex

object HTML5 extends directives.Events
                with directives.Bindings
                with schema.HTML {
  import org.scalajs.dom._
   
  def validityMessage(elem: HTMLInputElement) = { 
    val s = span()
    elem.addEventListener("input", { (e: Event) =>
      s.textContent = elem.validationMessage
    })
    s
  }
  
  object `class` {
    def invalid(elem: HTMLInputElement, c: String) = {
      elem.addEventListener("input", { (e: Event) =>
        if (elem.validity.valid)
          elem.classList.remove(c)
        else
          elem.classList.add(c)
      })
    }
  }
  
  implicit class RichHTMLInputElement(val elem: HTMLInputElement) extends AnyVal {
    def messages(implicit ec: ExecutionContext): clide.reactive.Event[Option[String]] = DOMEvent(elem,"input").sample(Option(elem.validationMessage))
  }
  
  implicit class RichHTMLLabelElement(val elem: HTMLLabelElement) extends AnyVal {
    def `for`: String = elem.htmlFor
    def for_=(value: String) = elem.htmlFor = value
  }   
  
  implicit class RichHTMLElement(val elem: HTMLElement) extends AnyVal {
    def text_=(value: String)  = elem.textContent = value
    def text: String           = elem.textContent
    def `class`: String        = elem.className
    def class_=(value: String) = elem.className = value    
    def role_=(value: String)  = elem.setAttribute("role", value)
    def role: String           = elem.getAttribute("role")
    
    def +=(other: Node): Unit = elem.appendChild(other)
    
    def +=(text: String): Unit = elem.appendChild(document.createTextNode(text))
    
    def +=(text: Bindable[String])(implicit ec: ExecutionContext): Unit = +=(text.watch)
    
    def +=(event: clide.reactive.Event[Node])(implicit ec: ExecutionContext): Unit = {
      var node = elem.appendChild(document.createComment("placeholder"))      
      event.foreach(newNode => { elem.replaceChild(newNode, node); node = newNode })
    }
    
    def +=(event: clide.reactive.Event[String])(implicit ec: ExecutionContext, d1: DummyImplicit): Unit = {
      var node = elem.appendChild(document.createTextNode(""))      
      event.foreach(node.textContent = _)
    }
    
    def +=(event: clide.reactive.Event[Option[Node]])(implicit ec: ExecutionContext, d1: DummyImplicit, d2: DummyImplicit): Unit = {
      elem += event.map {
        case None => document.createComment("placeholder")
        case Some(e) => e
      }
    } 
    
    def +=(event: clide.reactive.Event[Option[String]])(implicit ec: ExecutionContext, d1: DummyImplicit, d2: DummyImplicit, d3: DummyImplicit): Unit = {      
      elem.+=(event.map {
        case None => ""
        case Some(e) => e
      })(ec,d1)
    }
    
    def +=(xs: TraversableOnce[HTMLElement]): Unit = {
      for (child <- xs) {
        elem.appendChild(child)
      }
    }
    
    def +=[T <: HTMLElement](buf: ObservableBufferView[T])(implicit ec: ExecutionContext): Unit = {
      val beforeHead = elem.appendChild(document.createComment("before collection"))
      val afterLast = elem.appendChild(document.createComment("after collection"))
      buf.changes.foreach {
        case Reset =>
          var current = beforeHead.nextSibling
          while (current != afterLast) {
            val rem = current
            current = current.nextSibling
            rem.parentNode.removeChild(rem)
          }
        case Insert(Head,node) =>
          elem.insertBefore(node, beforeHead.nextSibling)
        case Insert(Last,node) =>
          elem.insertBefore(node, afterLast)
        case Insert(Index(i), node) =>
          var n = i
          var ref = beforeHead.nextSibling
          while (n > 0) {            
            ref = ref.nextSibling
            n -= 1
          }
          ref.parentNode.insertBefore(node, ref)
        case Remove(Head) =>
          elem.removeChild(beforeHead.nextSibling)
        case Remove(Last) =>
          elem.removeChild(afterLast.previousSibling)
        case Remove(Index(i)) =>
          var n = i
          var ref = beforeHead.nextSibling
          while (n > 0) {
            ref = ref.nextSibling
            n -= 1
          }
          elem.removeChild(ref)        
        case Update(Head,node) =>
          elem.replaceChild(node,beforeHead.nextSibling)
        case Update(Last,node) =>
          elem.replaceChild(node,afterLast.previousSibling)
        case Update(Index(i),node) =>
          var n = i
          var ref = beforeHead.nextSibling
          while (n > 0) {
            ref = ref.nextSibling
            n -= 1            
          }
          elem.replaceChild(node, ref)
      }
    }
  }    
}