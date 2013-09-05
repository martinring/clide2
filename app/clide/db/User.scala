package clide.db

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
    timeout: Option[Date]) extends GenericUser
    
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
  
  def getByEmail(email: String) = for {    
    user <- Users if user.email === email
  } yield user
  
  def getBySession(session: String) = for {
    user <- Users if user.session === session
  } yield user
}