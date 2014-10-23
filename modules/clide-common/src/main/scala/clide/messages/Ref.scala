package clide.messages

import scala.concurrent.Future

abstract class RefResolver[T,I](val resolve: I => Future[T])
  
sealed trait Ref[T,I] {
  def get(implicit resolver: RefResolver[T,I]): Future[T]
  def id: I
  
  override def equals(other: Any) = other match {
    case ref: Ref[_,_] => ref.id == this.id
    case _ => false
  }
}

case class Resolved[T,I](id: I, value: T) extends Ref[T,I] {
  def get(implicit resolver: RefResolver[T,I]) = Future.successful(value)
}

case class Unresolved[T,I](id: I) extends Ref[T,I] {
  def get(implicit resolver: RefResolver[T,I]) = resolver.resolve(id)
}
