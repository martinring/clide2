package clide.client.ui.html

import clide.client.rx.Observable

trait Action {
  def trigger(): Unit  
  def executable: Observable[Boolean]
  
  def when(possible: Observable[Boolean]) = Action(trigger(),possible)    
}

object Action {
  def apply(body: => Unit): Action = apply(body,Observable.from(true))
  
  def apply(body: => Unit, possible: Observable[Boolean]): Action = new Action {
    def trigger(): Unit = body
    def executable = possible
  }
}