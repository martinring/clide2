import angular.Angular
import html5.Window
import scala.scalajs.js

class App(angular: Angular, window: Window) {
  import window._
  import clide.collaboration._
  
  def start() {
    console.log("starting up")
    val op1 = Operation(List(Retain(5)))
    val op2 = Operation(List(Delete(2), Insert("hallo"), Retain(3)))
    val composed = Operation.compose(op1,op2)
    console.log(composed.get.toString)
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