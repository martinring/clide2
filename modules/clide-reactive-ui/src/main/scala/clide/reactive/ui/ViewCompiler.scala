package clide.reactive

import org.scalajs.dom
import org.scalajs.dom.DOMParser
import scala.annotation.tailrec
import org.scalajs.dom.NamedNodeMap
import scala.concurrent.ExecutionContext
import org.scalajs.dom.EventTarget
import clide.reactive.ui.events.DOMEvent

package object ui {/*
  val regex = "{{([0-9]+)}}".r

  /**
   * TODO: Make this a macro to get better runtime performance + static checking
   */
  implicit class ViewCompiler(val sc: StringContext) extends AnyVal {
    def html(args: ViewBinding[_]*)(implicit ec: ExecutionContext): View = {      
      var string = ""
      var id = -1
      for (part <- sc.parts) {
        if (id >= 0) args(id) match {          
          case StaticViewBinding(value) => 
            string += value      
          case EventViewBinding(e) =>
            string += "{{" + id ++ "}}"
        }
        string += part
        id += 1
      }      
      val parser = new DOMParser
      val nodes = parser.parseFromString(string, "text/html").body.childNodes
      def crawl(node: dom.Node): Unit = {
        if (node.nodeType == dom.Node.COMMENT_NODE) //
          ()
        else if (node.nodeType != dom.Node.TEXT_NODE && node.hasAttributes) {
          node.attributes.foreach { case (k,v) =>
            val matches = regex.findAllIn(v)
            if (matches.hasNext)
              println("found attribute: " + k + " -> " + v)
          }
          node.childNodes.foreach(crawl)
        }          
        else {          
          var text = node.textContent
          var current = regex findFirstMatchIn text
          var remove = current.isDefined
          while (current.isDefined) {
            val m = current.get
            if (m.start > 0) {
              node.parentNode.insertBefore(dom.document.createTextNode(text.take(m.start)), node)              
            }
            var inserted = (InsertionContext before node).insert(dom.document.createComment("placeholder"))
            args(m.group(1).toInt).asInstanceOf[EventViewBinding[_]].event.foreach { x =>
              inserted = inserted.replace.insert(dom.document.createTextNode(x.toString))
            }
            text = text.drop(m.end)
            current = regex findFirstMatchIn text
          }
          if (remove && text.nonEmpty) node.parentNode.replaceChild(dom.document.createTextNode(text), node)
          else if (remove) node.parentNode.removeChild(node)
        }
      }
      nodes.foreach(crawl)
      View { ic =>
        val inserted = nodes.map(ic.insert)
        () => inserted.foreach(_.remove())
      }
    }
  }
  
  implicit class RichHTMLCollection(val col: dom.NodeList) extends AnyVal {
    def foreach(f: dom.Node => Unit): Unit = 
      map(f)
            
    def map[A](f: dom.Node => A, start: Int = 0, accum: Seq[A] = Seq.empty[A]): Seq[A] =      
      if (start < col.length.toInt)
        map(f, start + 1, accum :+ f(col(start)))
      else
        accum
  }
  
  implicit class RichNamedNodeMap(val map: NamedNodeMap) extends AnyVal {
    def foreach(f: (String,String) => Unit, start: Int = 0): Unit =
      if (start < map.length.toInt) {
        val elem = map.apply(start)
        f(elem.name, elem.value)
      }        
  }
  
  implicit class RichEventTarget(val target: EventTarget) extends AnyVal {
    def on[E](name: String): Event[E] = DOMEvent(target,name)
  }
*/}