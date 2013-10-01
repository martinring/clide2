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
    password: String)
    
object UserInfo {
  implicit object Writes extends Writes[UserInfo] {
    def writes(u: UserInfo) = Json.obj(
        "name"  -> u.name, 
        "email" -> u.email) 
  }
}
    
