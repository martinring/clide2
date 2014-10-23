package clide.messages.projects

import clide.messages.Request

object Project {
  case class Create(name: String, public: Boolean)
  
  sealed trait CreationResponse
  case class CreationRefused(reason: CreationRefused.Reason) extends CreationResponse
  case class Created(info: ProjectInfo) extends CreationResponse
  
  object CreationRefused {
    sealed trait Reason extends Error
    case object InvalidName extends Reason
    case object NameNotUnique extends Reason
  }
}