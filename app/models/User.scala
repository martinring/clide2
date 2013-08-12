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
  def name     = column[String]("name", O.PrimaryKey)
  def email    = column[String]("email")
  def password = column[String]("password")
  def *        = name ~ email ~ password <> (User.apply _, User.unapply _)
  
  val getByName = for {
    name <- Parameters[String]
    user <- Users if user.name === name
  } yield user.*
  
  val getByEmail = for {
    email <- Parameters[String]
    user  <- Users if user.email === email
  } yield user.*
  
  val authenticate = for {
    (name,password) <- Parameters[(String,String)]
    user <- Users if user.name === name && user.password === password
  } yield user.*  
}