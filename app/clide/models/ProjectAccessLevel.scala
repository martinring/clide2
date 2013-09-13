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

object ProjectAccessLevel extends Enumeration {
  val None = Value(0)
  val Read = Value(1)
  val Write = Value(2)
  val Admin = Value(3) 
}

object ProjectAccessLevels extends Table[(Long,String,ProjectAccessLevel.Value)]("rights") {
  implicit val levelMapper = MappedTypeMapper.base[ProjectAccessLevel.Value, Int](
      _.id , ProjectAccessLevel.apply _)
  
  def projectId = column[Long]("project")
  def userName  = column[String]("user")
  def project   = foreignKey("fk_right_project", projectId, ProjectInfos)(_.id)
  def user      = foreignKey("fk_right_user", userName, UserInfos)(_.name)
  def pk        = primaryKey("pk_right", (projectId,userName))
  def level     = column[ProjectAccessLevel.Value]("policy")  
  def *         = projectId ~ userName ~ level
  
  def getUserProjects(user: String) = for {
    ai <- ProjectAccessLevels if ai.userName === user
    p  <- ai.project
  } yield (p, ai.level)
  
  def getProjectUsers(project: Long) = for {
    ai <- ProjectAccessLevels if ai.projectId === project    
  } yield (ai.userName -> ai.level)
}