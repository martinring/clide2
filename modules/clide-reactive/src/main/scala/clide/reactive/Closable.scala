package clide.reactive

trait Closable {
  def close()
  
  def merge(that: Closable) = Closable {
    this.close()
    that.close()
  }
}

object Closable {
  def apply(f: => Unit) = new Closable { def close() = f }
}