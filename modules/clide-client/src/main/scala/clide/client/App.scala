package clide.client

import scala.scalajs.js
import angular.js._
import angular.js.ng._

object App {  
  import scala.scalajs.js.JsGlobal._
  
  def run() {
    val clide = angular.module("clide", js.Array[js.String]())
    clide.controllercontroller("AppController", js.Array("$scope", { (scope: js.Dynamic) =>
	  scope.name = "It works"
	}))
	angular.element(JsGlobal.document).ready { () =>
	  console.log("hallo")
	  angular.bootstrap(document, js.Array[js.String]("clide"))
	}
    
    val editor = new IDirective {
      
    }
  }
}