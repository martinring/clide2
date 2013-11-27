package clide.client

import scala.scalajs.js
import clide.client.libs._

object App {    
  import DomGlobals._
  
  def init() {
    val clide = angular.module("clide", js.Array[js.String]())
    clide.controller("AppController", js.Array[js.Any]("$scope", { ($scope: js.Dynamic with IScope) =>      
	  $scope.name = "It works"
	}))
	angular.element(document.asInstanceOf[Element]).ready { () =>
	  console.log("ready")
	  angular.bootstrap(document, js.Array[js.Any]("clide"))
	}
  }
}