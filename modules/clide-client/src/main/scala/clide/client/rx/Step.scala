package clide.client.rx

trait Step[+T]
case class Next[T](val value: T) extends Step[T]
case class Error(val error: Throwable) extends Step[Nothing]
case object Completed extends Step[Nothing]