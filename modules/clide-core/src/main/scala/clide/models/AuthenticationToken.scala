package clide.models

trait AuthenticationToken
case object EmptyToken extends AuthenticationToken
case class  FullToken(user: String, key: String) extends AuthenticationToken