package clide.reactive.ui
import org.scalajs.dom
import scala.language.implicitConversions
import clide.reactive.Event
import scala.concurrent.ExecutionContext
import org.scalajs.dom.Node

trait View {
  def apply(ic: InsertionContext): InsertedView
}

trait InsertedView {
  def destroy(): Unit
}

object View {
  def apply(f: InsertionContext => (() => Unit)) = new View {
    def apply(ic: InsertionContext) = {
      val rem = f(ic)
      new InsertedView {
        def destroy() = rem()
      }
    }
  }
}