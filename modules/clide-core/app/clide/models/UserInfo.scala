package clide.models

import java.security.MessageDigest 

case class UserInfo(
    name: String, 
    email: String) {
  def withPassword(plain: String) = { // TODO: Think about security
    new UserInfo(name,email) with Password {
      val password = UserInfo.passwordHash(name,plain)
    }
  }
}

object UserInfo {
  def passwordHash(name: String, password: String) = 
    MessageDigest.getInstance("MD5").digest((name + password).getBytes("UTF-8"))
}

trait Password { self: UserInfo =>
  val password: Array[Byte]
}