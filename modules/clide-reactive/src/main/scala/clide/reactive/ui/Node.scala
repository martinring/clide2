package clide.reactive.ui

import clide.reactive.Event
import org.scalajs.dom.document

trait Node

class Div extends Node {
  private val elem = document.createElement("div")
  
  def click: Event[Unit] = ???
  
  
}