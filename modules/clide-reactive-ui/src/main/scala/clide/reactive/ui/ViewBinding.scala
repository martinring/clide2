package clide.reactive.ui

import clide.reactive.Event
import language.implicitConversions

trait ViewBinding[+A]
case class StaticViewBinding[A](value: A) extends ViewBinding[A]
case class EventViewBinding[A](event: Event[A]) extends ViewBinding[A]

object ViewBinding {  
  implicit def event[A](event: Event[A]) = EventViewBinding(event)
  implicit def static[A](value: A) = StaticViewBinding(value)
}