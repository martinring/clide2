package clide.client.util

trait Cancellable {
  def cancel()
  def isCancelled: Boolean
}

object Cancellable {
  def apply() = new Cancellable {
    def cancel() = {}
    def isCancelled = true
  }
  
  def apply(task: => Unit) = new Cancellable {
    private var cancelled = false
    def cancel() = if (!cancelled) { task; cancelled = true }
    def isCancelled = cancelled
  }
}