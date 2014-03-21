package clide.reactive.ui
import org.scalajs.dom
import scala.language.implicitConversions
import clide.reactive.Event
import scala.concurrent.ExecutionContext
import org.scalajs.dom.Node

trait View {
  def apply(ic: InsertionContext): InsertedNode
}