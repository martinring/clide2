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
    password: String,
    session: Option[String],
    timeout: Option[Date]) extends GenericUser
    
object UserInfos extends Table[UserInfo]("users") {  
  def name     = column[String]("name", O.PrimaryKey)
  def email    = column[String]("email")
  def password = column[String]("password")
  def session  = column[Option[String]]("session")
  def timeout  = column[Option[Date]]("timeout")
  def *        = name ~ email ~ password ~ session ~ timeout <> (UserInfo.apply _, UserInfo.unapply _)
  
  def getByName(name: String) = for {    
    user <- UserInfos; if user.name === name
  } yield user
  
  def getByEmail(email: String) = for {    
    user <- UserInfos if user.email === email
  } yield user
  
  def getBySession(session: String) = for {
    user <- UserInfos if user.session === session
  } yield user    
}