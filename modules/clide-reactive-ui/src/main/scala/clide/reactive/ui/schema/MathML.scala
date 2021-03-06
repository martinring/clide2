package clide.reactive.ui.schema

import org.scalajs.dom._

trait MathML {
  def math()             = document.createElement("math").asInstanceOf[Element]
  def maction()          = document.createElement("maction").asInstanceOf[Element]
  def menclose()         = document.createElement("menclose").asInstanceOf[Element]
  def merror()           = document.createElement("merror").asInstanceOf[Element]
  def mfenced()          = document.createElement("mfenced").asInstanceOf[Element]
  def mfrac()            = document.createElement("mfrac").asInstanceOf[Element]
  def mglyph()           = document.createElement("mglyph").asInstanceOf[Element]
  def mi()               = document.createElement("mi").asInstanceOf[Element]
  def mlabeldtr()        = document.createElement("mlabeldtr").asInstanceOf[Element]
  def mlongdiv()         = document.createElement("mlongdiv").asInstanceOf[Element]
  def mmultiscripts()    = document.createElement("mmultiscripts").asInstanceOf[Element]
  def mn()               = document.createElement("mn").asInstanceOf[Element]
  def mo()               = document.createElement("mo").asInstanceOf[Element]
  def mover()            = document.createElement("mover").asInstanceOf[Element]
  def mpadded()          = document.createElement("mpadded").asInstanceOf[Element]
  def mphantom()         = document.createElement("mphantom").asInstanceOf[Element]
  def mroot()            = document.createElement("mroot").asInstanceOf[Element]
  def mrow()             = document.createElement("mrow").asInstanceOf[Element]
  def ms()               = document.createElement("ms").asInstanceOf[Element]
  def mscarries()        = document.createElement("mscarries").asInstanceOf[Element]
  def mscarry()          = document.createElement("mscarry").asInstanceOf[Element]
  def msgroup()          = document.createElement("msgroup").asInstanceOf[Element]
  def msline  ()         = document.createElement("msline").asInstanceOf[Element]
  def mspace()           = document.createElement("mspace").asInstanceOf[Element]
  def msqrt()            = document.createElement("msqrt").asInstanceOf[Element]
  def msrow()            = document.createElement("msrow").asInstanceOf[Element]
  def mstack()           = document.createElement("mstack").asInstanceOf[Element]
  def mstyle()           = document.createElement("mstyle").asInstanceOf[Element]
  def msub()             = document.createElement("msub").asInstanceOf[Element]
  def msup()             = document.createElement("msup").asInstanceOf[Element]
  def msubsup()          = document.createElement("msubsup").asInstanceOf[Element]
  def mtable()           = document.createElement("mtable").asInstanceOf[Element]
  def mtd()              = document.createElement("mtd").asInstanceOf[Element]
  def mtext()            = document.createElement("mtext").asInstanceOf[Element]
  def mtr()              = document.createElement("mtr").asInstanceOf[Element]
  def munder()           = document.createElement("munder").asInstanceOf[Element]
  def munderover()       = document.createElement("munderover").asInstanceOf[Element]
  def semantics()        = document.createElement("semantices").asInstanceOf[Element]
  def annotation()       = document.createElement("annotation").asInstanceOf[Element]
  def `annotation-xml`() = document.createElement("annotation-xml").asInstanceOf[Element]
}