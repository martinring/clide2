package clide.core.projects

object Project {
  case class Create(name: String, public: Boolean)
  
  sealed trait CreationResponse
  case class CreationRefused(reason: CreationRefused.Reason) extends CreationResponse
  case class Created(info: ProjectInfo) extends CreationResponse
  
  object CreationRefused {
    sealed trait Reason
    case object InvalidName extends Reason
    case object NameNotUnique extends Reason
  }
}