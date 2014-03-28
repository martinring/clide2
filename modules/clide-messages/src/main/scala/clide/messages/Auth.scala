package clide.messages

object Auth {
  case class SignUp(username: String, email: String, password: String)      
  case class Login(username: String, password: String)  
  
  case class LoggedIn(token: String)
}