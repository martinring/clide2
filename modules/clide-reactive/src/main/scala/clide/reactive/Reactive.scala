package clide.reactive

import scala.util.control.NonFatal
import scala.util.Try
import scala.util.Success
import scala.util.Failure

sealed trait Reactive[-A] {
  
}

case object Ignoring extends Reactive[Any]
case class Accepting[A](next: Try[Option[A]] => Reactive[A]) extends Reactive[A]

object Reactive {
  def unfold[A,B](f: B => Option[(A,B)])(b: B): List[A] = ???
}