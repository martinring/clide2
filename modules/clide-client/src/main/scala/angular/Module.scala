package angular

import scala.scalajs.js

trait Module extends js.Object {
  def config(configFn: js.Array[js.Any])
  def controller(name: js.String, constructor: js.Array[js.Any])
  def directive(name: js.String, )
  def value(name: js.String, value: Any)
}

trait AngularDependency {
  val name: String
}

trait Controller[T <: js.Object] {
  val $scope: T
}