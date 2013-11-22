package html5

import scala.scalajs.js

trait Window extends js.Object {
  val document: DOMDocument
  val console: Console
  def alert(msg: js.String): Unit
}

trait Console extends js.Object {
  def log(args: js.Any*): js.Undefined
}

trait DOMDocument extends DOMElement {
  def getElementById(id: js.String): DOMElement
  def createElement(tag: js.String): DOMElement
}

trait DOMElement extends js.Object {
  var innerHTML: js.String
  def appendChild(child: DOMElement): Unit
}