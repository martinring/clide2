package clide.reactive

trait Continuous[A] {
  def now: A
}