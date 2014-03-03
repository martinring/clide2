package clide.client.ui

import clide.client.rx.Observable

trait Operation {
  def transform(that: Operation): (Operation,Operation)
  def compose(that: Operation): (Operation, Operation)
}

trait Token {
  
}

trait Editor {
  def applyOp(op: Operation)
  def changes: Observable[Operation]
}