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
import java.sql.Date 
import scala.slick.lifted.ForeignKeyAction

case class LoginInfo(
  user: String,
  key: String,
  timeout: Option[Date]
)

object LoginInfos extends Table[LoginInfo]("logins") {
  def userName = column[String]("user")
  def key      = column[String]("key")
  def timeout  = column[Option[Date]]("timeout")
  def user     = foreignKey("fk_login_user", userName, UserInfos)(_.name, 
      onUpdate = ForeignKeyAction.Cascade, 
      onDelete = ForeignKeyAction.Cascade)
      
  def *        = userName ~ key ~ timeout <> (LoginInfo.apply _, LoginInfo.unapply _)
  
  def delete(login: LoginInfo)(implicit session: Session) = {
    val q = for (l <- LoginInfos if l.key === login.key &&
                                    l.userName === login.user) yield l
    q.delete
  }
    
  
  def get(user: String, key: String) = for {
    login <- LoginInfos if login.userName === user && login.key === key
  } yield login
  
  def getForUser(user: String) = for {
    login <- LoginInfos if login.userName === user
  } yield login
  
  def getForKey(user: String) = for {
    login <- LoginInfos if login.key === key
  } yield login
}