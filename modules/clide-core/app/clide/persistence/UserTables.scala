package clide.persistence

import clide.models._
import java.sql.Date
import slick.lifted.ForeignKeyAction
import java.security.MessageDigest
import scala.slick.lifted.MappedProjection

trait UserTables { this: Profile =>
  import profile.simple._
  
  object UserInfos extends Table[UserInfo with Password]("users") {  
    def name     = column[String]("name", O.PrimaryKey)
    def email    = column[String]("email")
    def password = column[Array[Byte]]("password")
    def *        = name ~ email ~ password <> (UserInfoWithPassword.apply _, UserInfoWithPassword.unapply _)
    
    def get(name: String)(implicit session: Session) =
      Query(UserInfos).filter(_.name === name).firstOption
    
    def getAll(implicit session: Session) = 
      Query(UserInfos).elements
    
    def getByEmail(email: String)(implicit session: Session) =
      Query(UserInfos).filter(_.email === email).firstOption
      
    def authenticate(user: UserInfo with Password)(implicit session: Session) =
      Query(UserInfos).filter(_.name === user.name).filter(_.password === user.password).exists
    
    def insert(user: UserInfo with Password)(implicit session: Session) = {
      name ~ email ~ password insert (user.name, user.email, user.password)
    }
  }
    
  object LoginInfos extends Table[LoginInfo]("logins") {
    def userName = column[String]("user")
    def key      = column[String]("key")
    def timeout  = column[Option[Date]]("timeout")
    def user     = foreignKey("fk_login_user", userName, UserInfos)(_.name, 
        onUpdate = ForeignKeyAction.Cascade, 
        onDelete = ForeignKeyAction.Cascade)
        
    def *        = userName ~ key ~ timeout <> (LoginInfo.apply _, LoginInfo.unapply _)        
    
    def create(info: LoginInfo)(implicit session: Session) = {
      *.insert(info)
    }
        
    def getByUser(user: String)(implicit session: Session) =
      Query(LoginInfos).filter(_.userName === user).elements      
    
    def getByKey(key: String)(implicit session: Session) =
      Query(LoginInfos).filter(_.key === key).elements      
    
    def delete(login: LoginInfo)(implicit session: Session) =
      Query(LoginInfos).filter(_.key === login.key)
                       .filter(_.userName === login.user)
                       .delete
  }
}