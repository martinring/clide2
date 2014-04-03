package clide.reactive.ui

import clide.reactive._
import scala.language.implicitConversions
import scala.concurrent.ExecutionContext
import scala.reflect.ClassTag
import clide.reactive.ObservableBufferView
import scala.util.matching.Regex

object HTML5 extends directives.Events
                with directives.Bindings {
  import org.scalajs.dom._

  // root element
  def html() = document.createElement("html").asInstanceOf[HTMLElement]
  // document metadata
  def head() = document.createElement("head").asInstanceOf[HTMLHeadElement]
  def title() = document.createElement("title").asInstanceOf[HTMLTitleElement]
  def base() = document.createElement("base").asInstanceOf[HTMLBaseElement]
  def link() = document.createElement("link").asInstanceOf[HTMLLinkElement]
  def meta() = document.createElement("meta").asInstanceOf[HTMLMetaElement]
  def style() = document.createElement("style").asInstanceOf[HTMLStyleElement]
  // scripts
  def script() = document.createElement("script").asInstanceOf[HTMLScriptElement]
  def noscript() = document.createElement("noscript").asInstanceOf[HTMLDivElement]
  // sections          
  def body() = document.createElement("body").asInstanceOf[HTMLBodyElement]
  def h1() = document.createElement("h1").asInstanceOf[HTMLHeadingElement]
  def h2() = document.createElement("h2").asInstanceOf[HTMLHeadingElement]
  def h3() = document.createElement("h3").asInstanceOf[HTMLHeadingElement]
  def h4() = document.createElement("h4").asInstanceOf[HTMLHeadingElement]
  def h5() = document.createElement("h5").asInstanceOf[HTMLHeadingElement]
  def h6() = document.createElement("h6").asInstanceOf[HTMLHeadingElement]
  def section() = document.createElement("section").asInstanceOf[HTMLElement]
  def nav() = document.createElement("nav").asInstanceOf[HTMLElement]
  def aside() = document.createElement("aside").asInstanceOf[HTMLElement]
  def header() = document.createElement("header").asInstanceOf[HTMLElement]
  def footer() = document.createElement("footer").asInstanceOf[HTMLElement]
  def address() = document.createElement("address").asInstanceOf[HTMLElement]
  def main() = document.createElement("main").asInstanceOf[HTMLElement]
  // grouping
  def p() = document.createElement("p").asInstanceOf[HTMLParagraphElement]
  def hr() = document.createElement("hr").asInstanceOf[HTMLHRElement]
  def pre() = document.createElement("pre").asInstanceOf[HTMLPreElement]
  def blockquote() = document.createElement("blockquote").asInstanceOf[HTMLQuoteElement]
  def ol() = document.createElement("ol").asInstanceOf[HTMLOListElement]
  def ul() = document.createElement("ul").asInstanceOf[HTMLUListElement]
  def li() = document.createElement("li").asInstanceOf[HTMLLIElement]
  def dl() = document.createElement("dl").asInstanceOf[HTMLDListElement]
  def dt() = document.createElement("dt").asInstanceOf[HTMLDTElement]
  def dd() = document.createElement("dd").asInstanceOf[HTMLDDElement]
  def figure() = document.createElement("figure").asInstanceOf[HTMLElement]
  def figcaption() = document.createElement("figcaption").asInstanceOf[HTMLElement]
  def div() = document.createElement("div").asInstanceOf[HTMLDivElement]  
  // semantic
  def a() = document.createElement("a").asInstanceOf[HTMLAnchorElement]
  def em() = document.createElement("em").asInstanceOf[HTMLElement]
  def strong() = document.createElement("strong").asInstanceOf[HTMLElement]
  def small() = document.createElement("small").asInstanceOf[HTMLElement]
  def s() = document.createElement("s").asInstanceOf[HTMLElement]
  def cite() = document.createElement("cite").asInstanceOf[HTMLElement]
  def q() = document.createElement("q").asInstanceOf[HTMLQuoteElement]
  def dfn() = document.createElement("dfn").asInstanceOf[HTMLElement]
  def abbr() = document.createElement("abbr").asInstanceOf[HTMLElement]          
  def time() = document.createElement("time").asInstanceOf[HTMLElement]
  def code() = document.createElement("code").asInstanceOf[HTMLElement]
  def `var`() = document.createElement("var").asInstanceOf[HTMLElement]
  def samp() = document.createElement("samp").asInstanceOf[HTMLElement]
  def kbd() = document.createElement("kbd").asInstanceOf[HTMLElement]
  def sub() = document.createElement("sub").asInstanceOf[HTMLElement]
  def sup() = document.createElement("sup").asInstanceOf[HTMLElement]
  def i() = document.createElement("i").asInstanceOf[HTMLElement]
  def b() = document.createElement("b").asInstanceOf[HTMLElement]
  def u() = document.createElement("u").asInstanceOf[HTMLElement]
  def mark() = document.createElement("mark").asInstanceOf[HTMLElement]
  def ruby() = document.createElement("ruby").asInstanceOf[HTMLElement]
  def rt() = document.createElement("rt").asInstanceOf[HTMLElement]
  def rp() = document.createElement("rp").asInstanceOf[HTMLElement]
  def bdi() = document.createElement("bdi").asInstanceOf[HTMLElement]
  def bdo() = document.createElement("bdo").asInstanceOf[HTMLElement]
  def span() = document.createElement("span").asInstanceOf[HTMLSpanElement]
  def br() = document.createElement("br").asInstanceOf[HTMLBRElement]
  def wbr() = document.createElement("wbr").asInstanceOf[HTMLElement]
  //diff
  def ins() = document.createElement("ins").asInstanceOf[HTMLElement]
  def del() = document.createElement("del").asInstanceOf[HTMLElement]
  //embedded
  def img() = document.createElement("img").asInstanceOf[HTMLImageElement]
  def iframe() = document.createElement("iframe").asInstanceOf[HTMLIFrameElement]
  def embed() = document.createElement("embed").asInstanceOf[HTMLEmbedElement]
  def `object`() = document.createElement("object").asInstanceOf[HTMLObjectElement]
  def param() = document.createElement("param").asInstanceOf[HTMLParamElement]
  def video() = document.createElement("video").asInstanceOf[HTMLVideoElement]
  def audio() = document.createElement("audio").asInstanceOf[HTMLAudioElement]
  def source() = document.createElement("source").asInstanceOf[HTMLSourceElement]
  def track() = document.createElement("track").asInstanceOf[HTMLTrackElement]
  def canvas() = document.createElement("canvas").asInstanceOf[HTMLCanvasElement]
  def map() = document.createElement("map").asInstanceOf[HTMLMapElement]
  def area() = document.createElement("area").asInstanceOf[HTMLAreaElement]
  def svg() = document.createElement("svg").asInstanceOf[HTMLElement]
  def math() = document.createElement("math").asInstanceOf[HTMLElement]
  //tables
  def table() = document.createElement("table").asInstanceOf[HTMLTableElement]
  def caption() = document.createElement("caption").asInstanceOf[HTMLTableCaptionElement]
  def colgroup() = document.createElement("colgroup").asInstanceOf[HTMLElement]
  def col() = document.createElement("col").asInstanceOf[HTMLTableColElement]
  def tbody() = document.createElement("tbody").asInstanceOf[HTMLTableSectionElement]
  def thead() = document.createElement("thead").asInstanceOf[HTMLTableSectionElement]
  def tfoot() = document.createElement("tfoot").asInstanceOf[HTMLTableSectionElement]
  def tr() = document.createElement("tr").asInstanceOf[HTMLTableRowElement]
  def td() = document.createElement("td").asInstanceOf[HTMLTableCellElement]
  def th() = document.createElement("th").asInstanceOf[HTMLTableHeaderCellElement]
  // forms
  def form() = document.createElement("form").asInstanceOf[HTMLFormElement]
  def fieldset() = document.createElement("fieldset").asInstanceOf[HTMLFieldSetElement]
  def legend() = document.createElement("legend").asInstanceOf[HTMLLegendElement]
  def label() = document.createElement("label").asInstanceOf[HTMLLabelElement]
  def input() = document.createElement("input").asInstanceOf[HTMLInputElement]
  def button() = document.createElement("button").asInstanceOf[HTMLButtonElement]
  def select() = document.createElement("select").asInstanceOf[HTMLSelectElement]
  def datalist() = document.createElement("datalist").asInstanceOf[HTMLDataListElement]
  def optgroupt() = document.createElement("optgroupt").asInstanceOf[HTMLOptGroupElement]
  def option() = document.createElement("option").asInstanceOf[HTMLOptionElement]
  def textarea() = document.createElement("textarea").asInstanceOf[HTMLTextAreaElement]
  def keygen() = document.createElement("keygen").asInstanceOf[HTMLElement]
  def output() = document.createElement("output").asInstanceOf[HTMLElement]
  def progress() = document.createElement("progress").asInstanceOf[HTMLProgressElement]
  def meter() = document.createElement("meter").asInstanceOf[HTMLElement]
  // interactive
  def details() = document.createElement("details").asInstanceOf[HTMLElement]
  def summary() = document.createElement("summary").asInstanceOf[HTMLElement]
  def command() = document.createElement("command").asInstanceOf[HTMLElement]
  def menu() = document.createElement("menu").asInstanceOf[HTMLMenuElement]  
   
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
  
  implicit class RichHTMLLabelElement(val elem: HTMLLabelElement) extends AnyVal {
    def for_=(value: String) = elem.htmlFor = value
  }   
  
  implicit class RichHTMLElement(val elem: HTMLElement) extends AnyVal {
    def text_=(value: String)  = elem.textContent = value
    def text: String           = elem.textContent
    def class_=(value: String) = elem.className = value
    def `class`: String        = elem.className    
    def role_=(value: String)  = elem.setAttribute("role", value)
    def role: String           = elem.getAttribute("role")
    
    def +=(other: Node): Unit = elem.appendChild(other)
    def +=(text: String): Unit = elem.appendChild(document.createTextNode(text))
    def +=(text: Bindable[String])(implicit ec: ExecutionContext): Unit = +=(text.watch)
    def +=(event: clide.reactive.Event[Node])(implicit ec: ExecutionContext): Unit = {
      var node = elem.appendChild(document.createComment("placeholder"))      
      event.foreach(newNode => { elem.replaceChild(newNode, node); node = newNode })
    }
    def +=(event: clide.reactive.Event[String])(implicit ec: ExecutionContext, ev: ClassTag[String]): Unit = {
      var node = elem.appendChild(document.createTextNode(""))      
      event.foreach(node.textContent = _)
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