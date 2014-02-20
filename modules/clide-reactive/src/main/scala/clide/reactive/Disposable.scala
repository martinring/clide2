package clide.reactive

trait Disposable {
  def dispose()
  
  def andThen(that: Disposable) = Disposable {
    this.dispose()
    that.dispose()
  }
}

object Disposable {
  def apply(f: => Unit) = new Disposable {
    def dispos() = f
  }
}