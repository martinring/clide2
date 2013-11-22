package angular

import scala.scalajs.js._

trait JQLite extends Object {
  def addClass(className: String): JQLite
  def addClass(function: Function): JQLite
  def after()
  def append()
  def attr()
  def bind()
  def children()  
  def contents()
  def css()
  def data()
  def eq()
  def find()
  def hasClass()
  def html()
  def next()
  def on()
  def off()
  def parent()
  def prepend()
  def prop()
  def ready(fn: Function0[Any]): Any 
  def remove()
  def removeAttr()
  def removeClass()
  def removeData()
  def replaceWith()
  def text()
  def toggleClass()
  def triggerHandler()
  def unbind()  
  def wrap()
}
