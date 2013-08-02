package models.ot

trait Message
case class Register(name: String) extends Message
case class Initialize(revision: Int, document: Document) extends Message
case class Change(revision: Int, operation: Operation) extends Message
case class Error(message: String) extends Message

case object Acknowledgement extends Message