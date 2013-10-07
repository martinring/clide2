package clide.models

object ProjectAccessLevel extends Enumeration {
  val None = Value(0)
  val Read = Value(1)
  val Write = Value(2)
  val Admin = Value(3) 
}