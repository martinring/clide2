package clide.reactive.ui.internal

import scala.reflect.macros.Context
import org.scalajs.dom
import org.scalajs.dom.HTMLElement

object HTMLTagTypes {    
  def apply(tagName: String)(c: Context)(pos: c.Position): c.Type = tagName match {
    // metadata
    case "head" => c.typeOf[dom.HTMLHeadElement]
    case "title" => c.typeOf[dom.HTMLTitleElement]
    case "base" => c.typeOf[dom.HTMLBaseElement]
    case "link" => c.typeOf[dom.HTMLLinkElement]
    case "meta" => c.typeOf[dom.HTMLMetaElement]
    case "style" => c.typeOf[dom.HTMLStyleElement]                             
    //scripts
    case "script" => c.typeOf[dom.HTMLScriptElement]
    case "noscript" => c.typeOf[dom.HTMLDivElement]          
    // sections          
    case "body" => c.typeOf[dom.HTMLBodyElement]
    case "h1" | "h2" | "h3"
       | "h4" | "h5" | "h6" => c.typeOf[dom.HTMLHeadingElement]
    case "section" 
       | "nav" 
       | "aside" 
       | "header" 
       | "footer" 
       | "address" 
       | "main" => c.typeOf[HTMLElement]
    // grouping
    case "p" => c.typeOf[dom.HTMLParagraphElement]
    case "hr" => c.typeOf[dom.HTMLHRElement]
    case "pre" => c.typeOf[dom.HTMLPreElement]
    case "blockquote" => c.typeOf[dom.HTMLQuoteElement]
    case "ol" => c.typeOf[dom.HTMLOListElement]
    case "ul" => c.typeOf[dom.HTMLUListElement]
    case "li" => c.typeOf[dom.HTMLLIElement]
    case "dl" => c.typeOf[dom.HTMLDListElement]
    case "dt" => c.typeOf[dom.HTMLDTElement]
    case "dd" => c.typeOf[dom.HTMLDDElement]
    case "figure" 
       | "figcaption" => c.typeOf[HTMLElement]
    case "div" => c.typeOf[dom.HTMLDivElement]
    // semantic
    case "a" => c.typeOf[dom.HTMLAnchorElement]
    case "em" => c.typeOf[HTMLElement]
    case "strong" => c.typeOf[HTMLElement]
    case "small" => c.typeOf[HTMLElement]
    case "s" => c.typeOf[HTMLElement]
    case "cite" => c.typeOf[HTMLElement]
    case "q" => c.typeOf[dom.HTMLQuoteElement]
    case "dfn" => c.typeOf[HTMLElement]
    case "abbr" => c.typeOf[HTMLElement]          
    case "time" => c.typeOf[HTMLElement]
    case "code" => c.typeOf[HTMLElement]
    case "var" => c.typeOf[HTMLElement]
    case "samp" => c.typeOf[HTMLElement]
    case "kbd" => c.typeOf[HTMLElement]
    case "sub" => c.typeOf[HTMLElement]
    case "sup" => c.typeOf[HTMLElement]
    case "i" => c.typeOf[HTMLElement]
    case "b" => c.typeOf[HTMLElement]
    case "u" => c.typeOf[HTMLElement]
    case "mark" => c.typeOf[HTMLElement]
    case "ruby" => c.typeOf[HTMLElement]
    case "rt" => c.typeOf[HTMLElement]
    case "rp" => c.typeOf[HTMLElement]
    case "bdi" => c.typeOf[HTMLElement]
    case "bdo" => c.typeOf[HTMLElement]
    case "span" => c.typeOf[dom.HTMLSpanElement]
    case "br" => c.typeOf[dom.HTMLBRElement]
    case "wbr" => c.typeOf[HTMLElement]
    //diff
    case "ins" => c.typeOf[HTMLElement]
    case "del" => c.typeOf[HTMLElement]
    //embedded
    case "img" => c.typeOf[dom.HTMLImageElement]
    case "iframe" => c.typeOf[dom.HTMLIFrameElement]
    case "embed" => c.typeOf[dom.HTMLEmbedElement]
    case "object" => c.typeOf[dom.HTMLObjectElement]
    case "param" => c.typeOf[dom.HTMLParamElement]
    case "video" => c.typeOf[dom.HTMLVideoElement]
    case "audio" => c.typeOf[dom.HTMLAudioElement]
    case "source" => c.typeOf[dom.HTMLSourceElement]
    case "track" => c.typeOf[dom.HTMLTrackElement]
    case "canvas" => c.typeOf[dom.HTMLCanvasElement]
    case "map" => c.typeOf[dom.HTMLMapElement]
    case "area" => c.typeOf[dom.HTMLAreaElement]
    case "svg" => c.typeOf[HTMLElement]
    case "math" => c.typeOf[HTMLElement]
    //tables
    case "table" => c.typeOf[dom.HTMLTableElement]
    case "caption" => c.typeOf[dom.HTMLTableCaptionElement]
    case "colgroup" => c.typeOf[HTMLElement]
    case "col" => c.typeOf[dom.HTMLTableColElement]
    case "tbody" => c.typeOf[dom.HTMLTableSectionElement]
    case "thead" => c.typeOf[dom.HTMLTableSectionElement]
    case "tfoot" => c.typeOf[dom.HTMLTableSectionElement]
    case "tr" => c.typeOf[dom.HTMLTableRowElement]
    case "td" => c.typeOf[dom.HTMLTableCellElement]
    case "th" => c.typeOf[dom.HTMLTableHeaderCellElement]
    // forms
    case "form" => c.typeOf[dom.HTMLFormElement]
    case "fieldset" => c.typeOf[dom.HTMLFieldSetElement]
    case "legend" => c.typeOf[dom.HTMLLegendElement]
    case "label" => c.typeOf[dom.HTMLLabelElement]
    case "input" => c.typeOf[dom.HTMLInputElement]
    case "button" => c.typeOf[dom.HTMLButtonElement]
    case "select" => c.typeOf[dom.HTMLSelectElement]
    case "datalist" => c.typeOf[dom.HTMLDataListElement]
    case "optgroupt" => c.typeOf[dom.HTMLOptGroupElement]
    case "option" => c.typeOf[dom.HTMLOptionElement]
    case "textarea" => c.typeOf[dom.HTMLTextAreaElement]
    case "keygen" => c.typeOf[HTMLElement]
    case "output" => c.typeOf[HTMLElement]
    case "progress" => c.typeOf[dom.HTMLProgressElement]
    case "meter" => c.typeOf[HTMLElement]
    // interactive
    case "details" => c.typeOf[HTMLElement]
    case "summary" => c.typeOf[HTMLElement]
    case "command" => c.typeOf[HTMLElement]
    case "menu" => c.typeOf[dom.HTMLMenuElement]                    
    case other =>
      c.abort(pos, "tag unsupported in html5: " + other)
  }
}