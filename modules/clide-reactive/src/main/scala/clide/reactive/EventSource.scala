package clide.reactive

trait EventRef[+A] {
  def listen: Event[A]
}