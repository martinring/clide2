package clide.core.users

object Auth {  
  case class SignUp(data: UserInfo, password: String)

  sealed trait SignUpResponse  
  case class SignedUp(data: UserInfo) extends SignUpResponse    
  case class SignUpRefused(reason: SignUpRefused.Reason) extends SignUpResponse
  object SignUpRefused {
    sealed trait Reason
    case object InvalidName extends Reason
    case object InvalidEmail extends Reason
    case object InvalidPassword extends Reason
    case object NameNotUnique extends Reason
  }

  case class Login(username: String, password: String)

  sealed trait LoginResponse
  case class LoggedIn(token: Token.Full) extends LoginResponse
  case object LoginRefused extends LoginResponse

  case class Request(username: String,
                     token: Token,
                     id: Long,
                     message: Any)
  case object AuthenticationRefused
  case object AuthenticationTimedOut

  case class Response(id: Long, message: Any)

  sealed trait Token
  object Token {
    case class Full(key: String) extends Token
    case object Empty extends Token
  }
}