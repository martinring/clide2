package clide.reactive.ui

trait Component {
  protected def elem: org.scalajs.dom.Node
}

trait StaticComponent extends Component {
  protected val elem: org.scalajs.dom.Node
}

trait DynamicComponent extends Component{
  protected def elem: org.scalajs.dom.Node
}