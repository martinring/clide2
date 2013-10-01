package clide.persistence
import scala.slick.driver.ExtendedProfile
import scala.slick.session.Session
import clide.models._

trait Profile {
  val profile: ExtendedProfile   
}

class Database(override val profile: ExtendedProfile) extends 
  UserTables with ProjectTables with Mappers with Profile { 
  import profile.simple._
  
  val tables = Seq(
    Users,Projects,AccessLevels)
  
  def create(implicit session: Session): Unit = {
    tables.map(_.ddl).reduce(_++_).create
  }
}