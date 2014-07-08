package clide.core.users

import java.security.MessageDigest
import java.security.SecureRandom
import java.math.BigInteger

private object Security {
  private val md5 = MessageDigest.getInstance("MD5")
  private val secureRandom = new SecureRandom()
  
  def hash(email: String, password: String) = md5.digest((email+password).getBytes("UTF-8"))   
  def newToken = new BigInteger(130,secureRandom).toString(32)
  
  val namingPattern = "[a-z]+[a-z0-9-]*".r
  val minimumPasswordLength = 8
}
