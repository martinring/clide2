package clide.reactive.ui

trait Template[A] {
  def apply(model: A): View
}

trait View {
  def apply(ic: InsertionContext): InsertedView
}

trait InsertedView {
  def destroy(): Unit
}

object View {
  def apply(f: InsertionContext => (() => Unit)) = new View {
    def apply(ic: InsertionContext) = {
      def rem = f(ic)
      new InsertedView {
        def destroy() = rem()
      }
    }
  }
}

object Template { 
  def apply[A](f: (A,InsertionContext) => (() => Unit)) = new Template[A] {
    def apply(model: A) = new View {
      def apply(ic: InsertionContext) = {
        val g = f(model,ic)
        new InsertedView {
          def destroy() = g()
        }
      }
    }
  }
}