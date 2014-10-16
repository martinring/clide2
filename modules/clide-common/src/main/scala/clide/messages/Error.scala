package clide.messages

trait Error {
  def message: String
}

case class InternalError(message: String) extends Error