package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

case class User(id: Int, name: String, email: String, password: String)

object Users extends Table[User]("users") {
  def id       = column[Int]("id", O.PrimaryKey, O.AutoInc)
  def name     = column[String]("name")
  def email    = column[String]("email")
  def password = column[String]("password")
  def *        = id ~ name ~ email ~ password <> (User, User.unapply _)
}