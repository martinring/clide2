package clide.messages

object Authentication {
  case class SignUp(username: String, email: String, password: String)
  case class Login(username: String, password: String)
  
  trait LoginResponse
  case class LoggedIn(token: FullToken) extends LoginResponse
  case object Refused extends LoginResponse
  
  case class Authenticated(token: AuthenticationToken,
                           message: Any)
  case object AuthenticationRefused
  case object AuthenticationTimedOut
                           
  trait AuthenticationToken
  case class FullToken(content: String) extends AuthenticationToken
  case object EmptyToken extends AuthenticationToken
}