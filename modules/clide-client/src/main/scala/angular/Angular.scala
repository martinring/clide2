package angular

import scala.scalajs._
import scala.scalajs.js._
import html5._

trait Angular extends js.Object {
  def bind(self: Object, fn: Function, args: Any*): Function
  def bootstrap(element: DOMElement): Injector
  def bootstrap(element: DOMElement, modules: Array[String]): Injector   
  def copy[T](source: T): T
  def copy[T](source: T, destination: T): T
  def element(html: String): JQLite
  def element(elem: DOMElement): JQLite
  def equals[T](o1: T, o2: T): Boolean    
  def fromJson(json: String): Any
  def identity: Function
  def injector(modules: Array[String]): Function
  def isArray(value: Any): Boolean
  def isDate(value: Any): Boolean
  def isDefined(value: Any): Boolean
  def isElement(value: Any): Boolean
  def isFunction(value: Any): Boolean
  def isNumber(value: Any): Boolean
  def isObject(value: Any): Boolean
  def isString(value: Any): Boolean
  def isUndefined(value: Any): Boolean
  def lowercase(string: String): String
  def module(name: String, requires: Array[String]): Module
  def module(name: String, requires: Array[String], configFn: Function): Module
  def module(name: String, configFn: Function): Module  
  def noop: Undefined
  def toJson(obj: Any): String
  def toJson(obj: Any, pretty: Boolean): String
  def uppercase(string: String): String
  def version: {
    def full: String
    def major: Number
    def minor: Number
    def dot: Number
    def codeName: String
  }
}