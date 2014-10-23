package clide.reactive.sync

trait ToBeSynced {
  var x: Int  
}

class X extends ToBeSynced {
  def x: Int = 4
  def x_=(value: Int) = {}
}