package clide.collaboration

object MessageType extends Enumeration {
  val Info, Typing, Output, Warning, Error = Value
}

object HelpRequestType extends Enumeration {
  val Completion = Value
}

sealed trait Annotation
case class Class(name: String) extends Annotation
case class Tooltip(content: String) extends Annotation
case class Message(messageType: MessageType.Value, content: String) extends Annotation
case class Substitution(content: String) extends Annotation
case class Request(id: Long, requestType: HelpRequestType.Value) extends Annotation
case class Cursor(owner: Long) extends Annotation
case class Selection(owner: Long) extends Annotation
case class Entity(id: Long) extends Annotation
case class LocalReference(id: Long, kind: String = "Definition") extends Annotation
case class InternalReference(file: Long, id: Long, kind: String = "Definition") extends Annotation
case class ExternalReference(url: String, kind: String = "Definition") extends Annotation

case class Annotations(
    length: Int,
    annotations: Set[Annotation],
    children: Seq[Annotations]) {
  require(length >= 0, "annotations can't have negative length")
}