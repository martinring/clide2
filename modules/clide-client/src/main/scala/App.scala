import angular.Angular
import scala.scalajs.js._

class App(angular: Angular) {
  import clide.collaboration._
  def run() {
    val clide = angular.module("clide", js.Array[js.String]())
    clide.controller("AppController", js.Array("$scope", { (scope: js.Dynamic) =>
	  console.log("init controller")
	  scope.name = "It works"
	}))
	angular.element(document).ready { () =>
	  console.log("hallo")
	  angular.bootstrap(document, js.Array[js.String]("clide"))
	}
  }
}