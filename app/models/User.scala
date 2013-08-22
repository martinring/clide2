package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import play.api.libs.Crypto
import java.sql.Date
import play.api.libs.json._

case class User(
    name: String, 
    email: String, 
    password: String,
    session: Option[String],
    timeout: Option[Date]) {  
  lazy val socket = {
    val (out,channel) = Concurrent.broadcast[String]
    val in = Iteratee.foreach[String] { message =>
      println(message)
    }
  }
  
  lazy val gravatar = {                      
    val md5 = java.security.MessageDigest.getInstance("MD5")
    
    val bytes = md5.digest(email.trim.toLowerCase.getBytes("CP1252"))
    
    val sb = new StringBuffer
    
    for (byte <- bytes) sb.append(
      Integer.toHexString(byte & 0xFF | 0x100).substring(1,3))
    
    f"http://www.gravatar.com/avatar/${sb.toString}?d=identicon"
  }
}

object Users extends Table[User]("users") {  
  def name     = column[String]("name", O.PrimaryKey)
  def email    = column[String]("email")
  def password = column[String]("password")
  def session  = column[Option[String]]("session")
  def timeout  = column[Option[Date]]("timeout")
  def *        = name ~ email ~ password ~ session ~ timeout <> (User.apply _, User.unapply _)
  
  def getByName(name: String) = for {    
    user <- Users; if user.name === name
  } yield user
  
  val getByEmail = for {
    email <- Parameters[String]
    user  <- Users if user.email === email
  } yield user
  
  val authenticate = for {
    (name,password) <- Parameters[(String,String)]
    user <- Users if user.name === name && user.password === password
  } yield user.session
}