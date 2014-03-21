package clide.client.ui

import clide.reactive.ui._
import clide.reactive.ui.html.HTML5._
import org.scalajs.dom.Node

@view class Dialog {
  def appendChild(node: Node): Unit = content.appendChild(node)
  
  html"""
    <div class='dialogOuterContainer'>
      <div class='dialogInnerContainer'>
        <div class='dialog'>
          <div class='container' scala:name='content'/>
        </div>
      </div>
    </div>
  """
}