package clide.client

import scala.scalajs.js
import org.scalajs.angular._

object App {  
  import scala.scalajs.js.JsGlobal._
  
  def run() {
    val clide = angular.module("clide", js.Array[js.String]())
    clide.controllercontroller("AppController", js.Array("$scope", { (scope: js.Dynamic) =>
	  scope.name = "It works"
	}))
	angular.element(document).ready { () =>
	  console.log("hallo")
	  angular.bootstrap(document, js.Array[js.String]("clide"))
	}
  }
}