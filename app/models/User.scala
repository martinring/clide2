package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor

case class User(name: String, email: String, password: String) {  
  lazy val socket = {
    val (out,channel) = Concurrent.broadcast[String]
    val in = Iteratee.foreach[String] { message =>
      println(message)
    }
  }
}

object Users extends Table[User]("users") {  
  def name     = column[String]("name", O.PrimaryKey, O.AutoInc)
  def email    = column[String]("email")
  def password = column[String]("password")
  def *        = name ~ email ~ password <> (User, User.unapply _)
  
  def get(name: String) = for {
    user <- Users if user.name === name
  } yield user.*
}