package org.scalajs.angular

import org.scalajs.dom._
import scala.scalajs.js.annotation._

trait JqLite {
  // FIXME: def closest(selectors: Any): Array[Any] = ???
  @JSName("val")
  def value(): Dynamic = ???
  @JSName("val")
  def value(func: Function2[Any, Any, Any]): JqLite = ???
  @JSName("val")
  def value(value: Array[String]): JqLite = ???
  @JSName("val")
  def value(value: Number): JqLite = ???
  @JSName("val")
  def value(value: String): JqLite = ???
  def addClass(classNames: String): JqLite = ???
  def addClass(func: Function2[Any, Any, String]): JqLite = ???
  def after(content: Any*): JqLite = ???
  def after(func: Function1[Any, Any]): JqLite = ???
  def append(content: Any*): JqLite = ???
  def append(func: Function2[Any, Any, Any]): JqLite = ???
  def appendTo(target: Any): JqLite = ???
  @JSBracketAccess
  def apply(x: Number): HTMLElement = ???
  def attr(attributeName: String): String = ???
  def attr(attributeName: String, func: Function2[Any, Any, Any]): JqLite = ???
  def attr(attributeName: String, value: Any): JqLite = ???
  def attr(map: Any): JqLite = ???
  def bind(events: Any*): JqLite = ???
  def bind(eventType: String): JqLite = ???
  def bind(eventType: String, preventBubble: Boolean): JqLite = ???
  def children(): JqLite = ???
  override def clone(): JqLite = ???
  def clone(withDataAndEvents: Boolean): JqLite = ???
  def clone(withDataAndEvents: Boolean, deepWithDataAndEvents: Boolean): JqLite = ???
  def contents(): JqLite = ???
  def css(properties: Any): JqLite = ???
  def css(propertyName: Any, value: Any): JqLite = ???
  def css(propertyName: String): String = ???
  def css(propertyName: String, value: Any): JqLite = ???
  def css(propertyNames: Array[String]): String = ???
  def data(): Dynamic = ???
  def data(key: String): Dynamic = ???
  def data(key: String, value: Any): JqLite = ???
  def data(obj: Any): JqLite = ???
  def eq(index: Number): JqLite = ???
  def find(element: Any): JqLite = ???
  def find(obj: JqLite): JqLite = ???
  def find(selector: String): JqLite = ???
  def hasClass(className: String): Boolean = ???
  def html(): String = ???
  def html(htmlContent: Function2[Number, String, String]): JqLite = ???
  def html(htmlString: String): JqLite = ???
  def html(obj: JqLite): JqLite = ???
  def next(): JqLite = ???
  def off(): JqLite = ???
  def off(events: String): JqLite = ???
  def off(eventsMap: Any): JqLite = ???
  def on(events: String): JqLite = ???  
  def on(eventsMap: Any): JqLite = ???
  def parent(): JqLite = ???
  def prepend(content: Any*): JqLite = ???
  def prepend(func: Function2[Any, Any, Any]): JqLite = ???
  def prependTo(target: Any): JqLite = ???
  def prop(map: Any): JqLite = ???
  def prop(propertyName: String): Dynamic = ???
  def prop(propertyName: String, func: Function2[Any, Any, Any]): JqLite = ???
  def prop(propertyName: String, value: Any): JqLite = ???
  def ready(handler: Any): JqLite = ???
  def remove(): JqLite = ???
  def remove(selector: Any): JqLite = ???
  def removeAttr(attributeName: String): JqLite = ???
  def removeClass(): JqLite = ???
  def removeClass(className: String): JqLite = ???
  def removeClass(func: Function2[Any, Any, Any]): JqLite = ???
  def removeData(): JqLite = ???
  def removeData(nameOrList: Any): JqLite = ???
  def replaceWith(func: Any): JqLite = ???
  def text(): String = ???
  def text(textString: Any): JqLite = ???
  def text(textString: Function2[Number, String, String]): JqLite = ???
  def toggleClass(): JqLite = ???
  def toggleClass(className: String): JqLite = ???
  def toggleClass(className: String, swtch: Boolean): JqLite = ???
  def toggleClass(func: Function3[Any, Any, Any, Any]): JqLite = ???
  def toggleClass(swtch: Boolean): JqLite = ???
  def triggerHandler(eventType: String, extraParameters: Any*): Object = ???
  def unbind(): JqLite = ???
  def unbind(eventType: String): JqLite = ???
  def unbind(eventType: String, fls: Boolean): JqLite = ???
  def unbind(evt: Any): JqLite = ???
  def wrap(func: Function1[Any, Any]): JqLite = ???
  def wrap(wrappingElement: Any): JqLite = ???
  var length: Number = _
}
