package clide.reactive

import org.scalajs.dom._

package object ui {
  implicit class TemplateCompiler(val sc: StringContext) extends AnyVal {
    def html(args: Any*): View = {            
      val parser = new DOMParser()
      var string = ""
      var id = -1
      args.foreach(println)
      for (part <- sc.parts) {
        if (id >= 0) args(id) match {          
          case e: Event[_] =>
            string += "{{" + id ++ "}}"
          case x => x.toString()          
        }
        string += part
        id += 1
      }
      val parsed = parser.parseFromString(string, "text/html").body
      console.log(parsed)
      val result = document.createDocumentFragment()
      View { ic => 
        val inserted = ic.insert(result)
        () => inserted.remove()
      }      
    }
  }
}