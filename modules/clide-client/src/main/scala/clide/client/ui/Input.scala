package clide.client.ui

import clide.client.ui.html.NodeFactory
import clide.client.rx.Observable
import clide.client.ui.html._

object Input {
  def text: (Observable[String], NodeFactory) = {
    val t = Var("")
    val nf = TextBox()()
    (t,nf)
  } 
    
    
  def button: (Observable[Unit], NodeFactory) = 
}

