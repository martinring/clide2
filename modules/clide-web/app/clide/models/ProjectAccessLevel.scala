package clide.models

import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import Database.{threadLocalSession => session}
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID
import java.io.File
import play.api.Play
import scala.slick.lifted.ForeignKeyAction

object ProjectAccessLevel extends Enumeration {
  val None = Value(0)
  val Read = Value(1)
  val Write = Value(2)
  val Admin = Value(3) 
}