package clide.reactive

trait Cancellable {
  def cancel()
}

object Cancellable {
  def apply(f: => Unit) = new Cancellable {
    def cancel() = f
  }
}