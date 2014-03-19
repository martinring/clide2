package clide.reactive.ui.internal

import scala.reflect.macros.Context
import org.scalajs.dom

object HTMLTagTypes {    
  def apply(tagName: String)(c: Context)(pos: c.Position): Option[c.Type] = tagName match {
    // metadata
    case "head" => Some(c.typeOf[dom.HTMLHeadElement])
    case "title" => Some(c.typeOf[dom.HTMLTitleElement])
    case "base" => Some(c.typeOf[dom.HTMLBaseElement])
    case "link" => Some(c.typeOf[dom.HTMLLinkElement])
    case "meta" => Some(c.typeOf[dom.HTMLMetaElement])
    case "style" => Some(c.typeOf[dom.HTMLStyleElement])
    //scripts
    case "script" => Some(c.typeOf[dom.HTMLScriptElement])
    case "noscript" => Some(c.typeOf[dom.HTMLDivElement])
    // sections          
    case "body" => Some(c.typeOf[dom.HTMLBodyElement])
    case "h1" | "h2" | "h3"
       | "h4" | "h5" | "h6" => Some(c.typeOf[dom.HTMLHeadingElement])
    case "section"
       | "nav"
       | "aside"
       | "header"
       | "footer"
       | "address"
       | "main" => Some(c.typeOf[dom.HTMLElement])
    // grouping
    case "p" => Some(c.typeOf[dom.HTMLParagraphElement])
    case "hr" => Some(c.typeOf[dom.HTMLHRElement])
    case "pre" => Some(c.typeOf[dom.HTMLPreElement])
    case "blockquote" => Some(c.typeOf[dom.HTMLQuoteElement])
    case "ol" => Some(c.typeOf[dom.HTMLOListElement])
    case "ul" => Some(c.typeOf[dom.HTMLUListElement])
    case "li" => Some(c.typeOf[dom.HTMLLIElement])
    case "dl" => Some(c.typeOf[dom.HTMLDListElement])
    case "dt" => Some(c.typeOf[dom.HTMLDTElement])
    case "dd" => Some(c.typeOf[dom.HTMLDDElement])
    case "figure" 
       | "figcaption" => Some(c.typeOf[dom.HTMLElement])
    case "div" => Some(c.typeOf[dom.HTMLDivElement])
    // semantic
    case "a" => Some(c.typeOf[dom.HTMLAnchorElement])
    case "em" => Some(c.typeOf[dom.HTMLElement])
    case "strong" => Some(c.typeOf[dom.HTMLElement])
    case "small" => Some(c.typeOf[dom.HTMLElement])
    case "s" => Some(c.typeOf[dom.HTMLElement])
    case "cite" => Some(c.typeOf[dom.HTMLElement])
    case "q" => Some(c.typeOf[dom.HTMLQuoteElement])
    case "dfn" => Some(c.typeOf[dom.HTMLElement])
    case "abbr" => Some(c.typeOf[dom.HTMLElement]          )
    case "time" => Some(c.typeOf[dom.HTMLElement])
    case "code" => Some(c.typeOf[dom.HTMLElement])
    case "var" => Some(c.typeOf[dom.HTMLElement])
    case "samp" => Some(c.typeOf[dom.HTMLElement])
    case "kbd" => Some(c.typeOf[dom.HTMLElement])
    case "sub" => Some(c.typeOf[dom.HTMLElement])
    case "sup" => Some(c.typeOf[dom.HTMLElement])
    case "i" => Some(c.typeOf[dom.HTMLElement])
    case "b" => Some(c.typeOf[dom.HTMLElement])
    case "u" => Some(c.typeOf[dom.HTMLElement])
    case "mark" => Some(c.typeOf[dom.HTMLElement])
    case "ruby" => Some(c.typeOf[dom.HTMLElement])
    case "rt" => Some(c.typeOf[dom.HTMLElement])
    case "rp" => Some(c.typeOf[dom.HTMLElement])
    case "bdi" => Some(c.typeOf[dom.HTMLElement])
    case "bdo" => Some(c.typeOf[dom.HTMLElement])
    case "span" => Some(c.typeOf[dom.HTMLSpanElement])
    case "br" => Some(c.typeOf[dom.HTMLBRElement])
    case "wbr" => Some(c.typeOf[dom.HTMLElement])
    //diff
    case "ins" => Some(c.typeOf[dom.HTMLElement])
    case "del" => Some(c.typeOf[dom.HTMLElement])
    //embedded
    case "img" => Some(c.typeOf[dom.HTMLImageElement])
    case "iframe" => Some(c.typeOf[dom.HTMLIFrameElement])
    case "embed" => Some(c.typeOf[dom.HTMLEmbedElement])
    case "object" => Some(c.typeOf[dom.HTMLObjectElement])
    case "param" => Some(c.typeOf[dom.HTMLParamElement])
    case "video" => Some(c.typeOf[dom.HTMLVideoElement])
    case "audio" => Some(c.typeOf[dom.HTMLAudioElement])
    case "source" => Some(c.typeOf[dom.HTMLSourceElement])
    case "track" => Some(c.typeOf[dom.HTMLTrackElement])
    case "canvas" => Some(c.typeOf[dom.HTMLCanvasElement])
    case "map" => Some(c.typeOf[dom.HTMLMapElement])
    case "area" => Some(c.typeOf[dom.HTMLAreaElement])
    case "svg" => Some(c.typeOf[dom.HTMLElement])
    case "math" => Some(c.typeOf[dom.HTMLElement])
    //tables
    case "table" => Some(c.typeOf[dom.HTMLTableElement])
    case "caption" => Some(c.typeOf[dom.HTMLTableCaptionElement])
    case "colgroup" => Some(c.typeOf[dom.HTMLElement])
    case "col" => Some(c.typeOf[dom.HTMLTableColElement])
    case "tbody" => Some(c.typeOf[dom.HTMLTableSectionElement])
    case "thead" => Some(c.typeOf[dom.HTMLTableSectionElement])
    case "tfoot" => Some(c.typeOf[dom.HTMLTableSectionElement])
    case "tr" => Some(c.typeOf[dom.HTMLTableRowElement])
    case "td" => Some(c.typeOf[dom.HTMLTableCellElement])
    case "th" => Some(c.typeOf[dom.HTMLTableHeaderCellElement])
    // forms
    case "form" => Some(c.typeOf[dom.HTMLFormElement])
    case "fieldset" => Some(c.typeOf[dom.HTMLFieldSetElement])
    case "legend" => Some(c.typeOf[dom.HTMLLegendElement])
    case "label" => Some(c.typeOf[dom.HTMLLabelElement])
    case "input" => Some(c.typeOf[dom.HTMLInputElement])
    case "button" => Some(c.typeOf[dom.HTMLButtonElement])
    case "select" => Some(c.typeOf[dom.HTMLSelectElement])
    case "datalist" => Some(c.typeOf[dom.HTMLDataListElement])
    case "optgroupt" => Some(c.typeOf[dom.HTMLOptGroupElement])
    case "option" => Some(c.typeOf[dom.HTMLOptionElement])
    case "textarea" => Some(c.typeOf[dom.HTMLTextAreaElement])
    case "keygen" => Some(c.typeOf[dom.HTMLElement])
    case "output" => Some(c.typeOf[dom.HTMLElement])
    case "progress" => Some(c.typeOf[dom.HTMLProgressElement])
    case "meter" => Some(c.typeOf[dom.HTMLElement])
    // interactive
    case "details" => Some(c.typeOf[dom.HTMLElement])
    case "summary" => Some(c.typeOf[dom.HTMLElement])
    case "command" => Some(c.typeOf[dom.HTMLElement])
    case "menu" => Some(c.typeOf[dom.HTMLMenuElement])
    case other => None
  }
}