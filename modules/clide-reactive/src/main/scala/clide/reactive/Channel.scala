package clide.reactive

trait Channel[-A] {
  def push(a: => A)
  def failure(e: Throwable)
  def close()
}

object Channel {
  def apply[A](f: A => Unit)(e: Throwable => Unit)(c: => Unit) = new Channel[A] {
    def push(a: => A) = f(a)
    def failure(t: Throwable) = e(t)
    def close() = c
  } 
}