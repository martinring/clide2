package clide.models

import scala.slick.driver.H2Driver.simple._
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import play.api.libs.Crypto
import java.sql.Date
import play.api.libs.json._

case class UserInfo(
    name: String, 
    email: String, 
    password: String) extends GenericUser
    
object UserInfo {
  implicit object Writes extends Writes[UserInfo] {
    def writes(u: UserInfo) = Json.obj(
        "name"  -> u.name, 
        "email" -> u.email) 
  }
}
    
object UserInfos extends Table[UserInfo]("users") {  
  def name     = column[String]("name", O.PrimaryKey)
  def email    = column[String]("email")
  def password = column[String]("password")
  def *        = name ~ email ~ password  <> (UserInfo.apply _, UserInfo.unapply _)
  
  def getByName(name: String) = for {    
    user <- UserInfos; if user.name === name
  } yield user
  
  def getByEmail(email: String) = for {    
    user <- UserInfos if user.email === email
  } yield user
  
  def passwordHash(name: String, password: String) = 
    Crypto.sign(name + password)
}