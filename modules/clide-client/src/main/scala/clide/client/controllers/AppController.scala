package clide.client.controllers

import clide.client.libs._
import scala.scalajs.js

trait AppScope extends IScope {
  var user: String    = null
  var version: String = null
  var date: js.Date   = null
  var goBack: Function0[Unit] = null
  var logout: Function0[Unit] = null
}

trait AppController extends Controller with Dependencies("$scope","$location","Auth","Toasts","version","date") {
  
}