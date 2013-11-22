package angular

import scala.scalajs.js

trait Module extends js.Object {
  def controller(name: js.String, constructor: js.Array[js.Any])
}