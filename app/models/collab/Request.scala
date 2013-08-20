package models.collab

trait Request
case class Register(name: String) extends Request
case class Initialize(revision: Int, document: Document) extends Request
case class Change(revision: Int, operation: Operation) extends Request
case class Error(message: String) extends Request

trait Reply
case object Acknowledgement extends Reply