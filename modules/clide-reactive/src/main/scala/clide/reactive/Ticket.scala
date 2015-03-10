package clide.reactive

trait Ticket {
  def cancel()
}

object Ticket {
  def apply(f: => Unit) = new Ticket {
    def cancel() = f
  }
}