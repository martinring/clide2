package clide.client.ui

import clide.reactive.ui._
import clide.reactive.ui.html.HTML5._

object Test {
  val a = <xml></xml>
}

@view class Main {
  <specificTag></specificTag>
  
  html"""
    <div id='hallo' scala:name='test'>
      <Login/>
    </div>
  """    
}
