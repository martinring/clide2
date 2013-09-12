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

object ProjectAccessInfos extends Table[(Long,String,Int)]("rights") {  
  def projectId = column[Long]("project")
  def userName  = column[String]("user")
  def project   = foreignKey("fk_right_project", projectId, ProjectInfos)(_.id)
  def user      = foreignKey("fk_right_user", userName, UserInfos)(_.name)
  def pk        = primaryKey("pk_right", (projectId,userName))
  def policy    = column[Int]("policy")  
  def *         = projectId ~ userName ~ policy
  
  val None = 0
  val Read = 1
  val Write = 2
  val Admin = 3
}