package clide.messages.users

object Auth {  
  case class SignUp(username: String, email: String, password: String, isHuman: Boolean)

  sealed trait SignUpResponse
  case class SignedUp(username: String, email: String) extends SignUpResponse
  case class SignUpRefused(reason: Seq[SignUpRefused.Reason]) extends SignUpResponse
  object SignUpRefused {
    sealed trait Reason extends Error
    case object InvalidName extends Reason
    case object InvalidEmail extends Reason
    case object InvalidPassword extends Reason
    case object NameNotUnique extends Reason
  }

  case class Login(username: String, password: String)

  sealed trait LoginResponse
  case class LoggedIn(token: AuthenticationToken.Full) extends LoginResponse
  case object LoginRefused extends LoginResponse
  
  case object Logout
  
  case class Request[+T](
      token: AuthenticationToken,
      message: T)

  sealed trait AuthenticationToken
  
  object AuthenticationToken {
    case class Full(username: String, key: String) extends AuthenticationToken
    case object Empty extends AuthenticationToken
  }
}