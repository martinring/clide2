package clide.client.util

import scala.scalajs.js
import scala.scalajs.js.JSConverters._
import org.scalajs.dom.document
import org.scalajs.dom.console
import org.scalajs.dom.raw.HTMLSpanElement
import scala.scalajs.js.annotation.JSExport

@JSExport
object Fonts {
  private lazy val container = {
    val result = document.createElement("span").asInstanceOf[HTMLSpanElement]
    result.style.position = "absolute"
    result.style.fontSize = "128px"
    result.style.left = "-99999px"
    result.innerHTML = "abcdefghijklmnopqrstuvwxyz0123456789!\"§$%&/()=?"
    result
  }
      
  private def calculateWidth(name: String) = {
    container.style.fontFamily = name
    document.body.appendChild(container)
    val width = container.clientWidth
    document.body.removeChild(container)
    width
  }
  
  private lazy val monoWidth = calculateWidth("monospace")
  private lazy val sansWidth = calculateWidth("sans-serif")
  
  @JSExport
  def isAvailable(name: String) = {
    if (monoWidth == sansWidth)
      console.warn("monospace and sans-serif width are equal. The result of Fonts.isAvailable will not be reliable")    
    monoWidth != calculateWidth(s"$name, monospace") || sansWidth != calculateWidth(s"$name, sans-serif")
  }
  
  @JSExport
  lazy val availableMonospaceFonts = 
    Array("Isabelle Text", "Inconsolata", "Consolas", 
      "Monaco", "DejaVu Sans Mono", "Ubuntu Mono", "Menlo",
      "Bitstream Vera Sans Mono", "Lucida Console",
      "Courier New", "Droid Sans Mono",
      "Latin Modern Mono", "monospace").filter(isAvailable).toJSArray
    
  @JSExport
  lazy val availableMathFonts = 
    Array("Computer Modern", "Cambria Math", "serif").filter(isAvailable).toJSArray    
}