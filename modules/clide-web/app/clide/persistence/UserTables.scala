package clide.persistence

import clide.models._
import play.api.libs.Crypto
import java.sql.Date
import slick.lifted.ForeignKeyAction

trait UserTables { this: Profile =>
  import profile.simple._
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
}