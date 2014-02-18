package clide.reactive.ui

import clide.reactive.Event

class Button extends NodeFactory {
  def click: Event[Unit]
}