package clide.reactive.ui.html

import clide.reactive.ui.View
import clide.reactive.ui.InsertionContext
import scala.language.implicitConversions

object HTML5 {
  import org.scalajs.dom._
  // root element
  @inline def html() = document.createElement("html").asInstanceOf[HTMLElement]
  // document metadata
  @inline def head() = document.createElement("head").asInstanceOf[HTMLHeadElement]
  @inline def title() = document.createElement("title").asInstanceOf[HTMLTitleElement]
  @inline def base() = document.createElement("base").asInstanceOf[HTMLBaseElement]
  @inline def link() = document.createElement("link").asInstanceOf[HTMLLinkElement]
  @inline def meta() = document.createElement("meta").asInstanceOf[HTMLMetaElement]
  @inline def style() = document.createElement("style").asInstanceOf[HTMLStyleElement]
  // scripts
  @inline def script() = document.createElement("script").asInstanceOf[HTMLScriptElement]
  @inline def noscript() = document.createElement("noscript").asInstanceOf[HTMLDivElement]
  // sections          
  @inline def body() = document.createElement("body").asInstanceOf[HTMLBodyElement]
  @inline def h1() = document.createElement("h1").asInstanceOf[HTMLHeadingElement]
  @inline def h2() = document.createElement("h2").asInstanceOf[HTMLHeadingElement]
  @inline def h3() = document.createElement("h3").asInstanceOf[HTMLHeadingElement]
  @inline def h4() = document.createElement("h4").asInstanceOf[HTMLHeadingElement]
  @inline def h5() = document.createElement("h5").asInstanceOf[HTMLHeadingElement]
  @inline def h6() = document.createElement("h6").asInstanceOf[HTMLHeadingElement]
  @inline def section() = document.createElement("section").asInstanceOf[HTMLElement]
  @inline def nav() = document.createElement("nav").asInstanceOf[HTMLElement]
  @inline def aside() = document.createElement("aside").asInstanceOf[HTMLElement]
  @inline def header() = document.createElement("header").asInstanceOf[HTMLElement]
  @inline def footer() = document.createElement("footer").asInstanceOf[HTMLElement]
  @inline def address() = document.createElement("address").asInstanceOf[HTMLElement]
  @inline def main() = document.createElement("main").asInstanceOf[HTMLElement]
  // grouping
  @inline def p() = document.createElement("p").asInstanceOf[HTMLParagraphElement]
  @inline def hr() = document.createElement("hr").asInstanceOf[HTMLHRElement]
  @inline def pre() = document.createElement("pre").asInstanceOf[HTMLPreElement]
  @inline def blockquote() = document.createElement("blockquote").asInstanceOf[HTMLQuoteElement]
  @inline def ol() = document.createElement("ol").asInstanceOf[HTMLOListElement]
  @inline def ul() = document.createElement("ul").asInstanceOf[HTMLUListElement]
  @inline def li() = document.createElement("li").asInstanceOf[HTMLLIElement]
  @inline def dl() = document.createElement("dl").asInstanceOf[HTMLDListElement]
  @inline def dt() = document.createElement("dt").asInstanceOf[HTMLDTElement]
  @inline def dd() = document.createElement("dd").asInstanceOf[HTMLDDElement]
  @inline def figure() = document.createElement("figure").asInstanceOf[HTMLElement]
  @inline def figcaption() = document.createElement("figcaption").asInstanceOf[HTMLElement]
  @inline def div() = document.createElement("div").asInstanceOf[HTMLDivElement]
  // semantic
  @inline def a() = document.createElement("a").asInstanceOf[HTMLAnchorElement]
  @inline def em() = document.createElement("em").asInstanceOf[HTMLElement]
  @inline def strong() = document.createElement("strong").asInstanceOf[HTMLElement]
  @inline def small() = document.createElement("small").asInstanceOf[HTMLElement]
  @inline def s() = document.createElement("s").asInstanceOf[HTMLElement]
  @inline def cite() = document.createElement("cite").asInstanceOf[HTMLElement]
  @inline def q() = document.createElement("q").asInstanceOf[HTMLQuoteElement]
  @inline def dfn() = document.createElement("dfn").asInstanceOf[HTMLElement]
  @inline def abbr() = document.createElement("abbr").asInstanceOf[HTMLElement]          
  @inline def time() = document.createElement("time").asInstanceOf[HTMLElement]
  @inline def code() = document.createElement("code").asInstanceOf[HTMLElement]
  @inline def `var`() = document.createElement("var").asInstanceOf[HTMLElement]
  @inline def samp() = document.createElement("samp").asInstanceOf[HTMLElement]
  @inline def kbd() = document.createElement("kbd").asInstanceOf[HTMLElement]
  @inline def sub() = document.createElement("sub").asInstanceOf[HTMLElement]
  @inline def sup() = document.createElement("sup").asInstanceOf[HTMLElement]
  @inline def i() = document.createElement("i").asInstanceOf[HTMLElement]
  @inline def b() = document.createElement("b").asInstanceOf[HTMLElement]
  @inline def u() = document.createElement("u").asInstanceOf[HTMLElement]
  @inline def mark() = document.createElement("mark").asInstanceOf[HTMLElement]
  @inline def ruby() = document.createElement("ruby").asInstanceOf[HTMLElement]
  @inline def rt() = document.createElement("rt").asInstanceOf[HTMLElement]
  @inline def rp() = document.createElement("rp").asInstanceOf[HTMLElement]
  @inline def bdi() = document.createElement("bdi").asInstanceOf[HTMLElement]
  @inline def bdo() = document.createElement("bdo").asInstanceOf[HTMLElement]
  @inline def span() = document.createElement("span").asInstanceOf[HTMLSpanElement]
  @inline def br() = document.createElement("br").asInstanceOf[HTMLBRElement]
  @inline def wbr() = document.createElement("wbr").asInstanceOf[HTMLElement]
  //diff
  @inline def ins() = document.createElement("ins").asInstanceOf[HTMLElement]
  @inline def del() = document.createElement("del").asInstanceOf[HTMLElement]
  //embedded
  @inline def img() = document.createElement("img").asInstanceOf[HTMLImageElement]
  @inline def iframe() = document.createElement("iframe").asInstanceOf[HTMLIFrameElement]
  @inline def embed() = document.createElement("embed").asInstanceOf[HTMLEmbedElement]
  @inline def `object`() = document.createElement("object").asInstanceOf[HTMLObjectElement]
  @inline def param() = document.createElement("param").asInstanceOf[HTMLParamElement]
  @inline def video() = document.createElement("video").asInstanceOf[HTMLVideoElement]
  @inline def audio() = document.createElement("audio").asInstanceOf[HTMLAudioElement]
  @inline def source() = document.createElement("source").asInstanceOf[HTMLSourceElement]
  @inline def track() = document.createElement("track").asInstanceOf[HTMLTrackElement]
  @inline def canvas() = document.createElement("canvas").asInstanceOf[HTMLCanvasElement]
  @inline def map() = document.createElement("map").asInstanceOf[HTMLMapElement]
  @inline def area() = document.createElement("area").asInstanceOf[HTMLAreaElement]
  @inline def svg() = document.createElement("svg").asInstanceOf[HTMLElement]
  @inline def math() = document.createElement("math").asInstanceOf[HTMLElement]
  //tables
  @inline def table() = document.createElement("table").asInstanceOf[HTMLTableElement]
  @inline def caption() = document.createElement("caption").asInstanceOf[HTMLTableCaptionElement]
  @inline def colgroup() = document.createElement("colgroup").asInstanceOf[HTMLElement]
  @inline def col() = document.createElement("col").asInstanceOf[HTMLTableColElement]
  @inline def tbody() = document.createElement("tbody").asInstanceOf[HTMLTableSectionElement]
  @inline def thead() = document.createElement("thead").asInstanceOf[HTMLTableSectionElement]
  @inline def tfoot() = document.createElement("tfoot").asInstanceOf[HTMLTableSectionElement]
  @inline def tr() = document.createElement("tr").asInstanceOf[HTMLTableRowElement]
  @inline def td() = document.createElement("td").asInstanceOf[HTMLTableCellElement]
  @inline def th() = document.createElement("th").asInstanceOf[HTMLTableHeaderCellElement]
  // forms
  @inline def form() = document.createElement("form").asInstanceOf[HTMLFormElement]
  @inline def fieldset() = document.createElement("fieldset").asInstanceOf[HTMLFieldSetElement]
  @inline def legend() = document.createElement("legend").asInstanceOf[HTMLLegendElement]
  @inline def label() = document.createElement("label").asInstanceOf[HTMLLabelElement]
  @inline def input() = document.createElement("input").asInstanceOf[HTMLInputElement]
  @inline def button() = document.createElement("button").asInstanceOf[HTMLButtonElement]
  @inline def select() = document.createElement("select").asInstanceOf[HTMLSelectElement]
  @inline def datalist() = document.createElement("datalist").asInstanceOf[HTMLDataListElement]
  @inline def optgroupt() = document.createElement("optgroupt").asInstanceOf[HTMLOptGroupElement]
  @inline def option() = document.createElement("option").asInstanceOf[HTMLOptionElement]
  @inline def textarea() = document.createElement("textarea").asInstanceOf[HTMLTextAreaElement]
  @inline def keygen() = document.createElement("keygen").asInstanceOf[HTMLElement]
  @inline def output() = document.createElement("output").asInstanceOf[HTMLElement]
  @inline def progress() = document.createElement("progress").asInstanceOf[HTMLProgressElement]
  @inline def meter() = document.createElement("meter").asInstanceOf[HTMLElement]
  // interactive
  @inline def details() = document.createElement("details").asInstanceOf[HTMLElement]
  @inline def summary() = document.createElement("summary").asInstanceOf[HTMLElement]
  @inline def command() = document.createElement("command").asInstanceOf[HTMLElement]
  @inline def menu() = document.createElement("menu").asInstanceOf[HTMLMenuElement]
    
  implicit def stringNode(s: String) = document.createTextNode(s)
  
  implicit class RichHTLLabelElement(val elem: HTMLLabelElement) extends AnyVal {
    def for_=(value: String) = elem.htmlFor = value
  }
  
  implicit class RichHTMLElement(val elem: HTMLElement) extends AnyVal {
    def text_=(value: String)  = elem.textContent = value
    def text: String           = elem.textContent
    def class_=(value: String) = elem.className = value
    def `class`: String        = elem.className    
    def role_=(value: String)  = elem.setAttribute("role", value)
    def role: String           = elem.getAttribute("role")
    
    def +=(other: Node) = elem.appendChild(other)
  }    
}