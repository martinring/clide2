package clide.persistence
import clide.models._

trait UserTables { this: Profile =>
  import profile.simple._
    
  object Users extends Table[(String,String,String)]("USERS") {    
    def name  = column[String]("NAME", O.PrimaryKey)
    def email = column[String]("EMAIL", O.NotNull)
    def passwordHash = column[String]("PASSWORD_HASH", O.NotNull)
    def * = name ~ email ~ passwordHash        
    
    def user = name ~ email <> (User.apply _, User.unapply _) 
    
    def insert(user: User with Password)(implicit session: Session) = {
      * insert (user.name, user.email, user.password)
    }
    
    def delete(user: User)(implicit session: Session) = {
      Query(Users).filter(_.name === user.name).delete
    }
    
    def byName(name: String)(implicit session: Session): Option[User] = {
      Query(Users).filter(_.name === name).map(_.user).firstOption
    }
    
    def all(implicit session: Session) = {
      Query(Users).map(_.user).elements
    }
  }
}