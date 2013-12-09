package clide.assistants

/*trait OptionType[T] {
  def name: String
  def serialize: T => String
  def deserialize: String => T
}

object OptionTypes {
  implicit object intOption extends OptionType[Int] {
    val name = "number"
    val serialize = (v: Int) => v.toString
    val deserialize = (s: String) => s.toInt
  }
  
  implicit object stringOption extends OptionType[String] {
    val name = "string"
    val serialize = identity[String] _
    val deserialize = identity[String] _
  }
  
  implicit object booleanOption extends OptionType[Boolean] {
    val name = "boolean"
    val serialize = (b: Boolean) => b.toString
    val deserialize = (s: String) => s.toBoolean
  }
  
  implicit def enumOption[T <: Enumeration](implicit t: T) = new OptionType[t.ValueSet] {
    val name = "{" + t.values.mkString(",") + "}"
    val serialize = (v: t.ValueSet) => v.map(_.toString).mkString(",")
    val deserialize = (s: String) => s.split(',').map(t.withName(_))
  }
}

trait AssistantOptions {
  def Option[T <% OptionType[T]](v: T)(implicit t: OptionType[T]) = ???
}*/