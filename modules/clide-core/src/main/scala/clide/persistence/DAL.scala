package clide.persistence

import scala.slick.driver.ExtendedDriver

class DAL(override val profile: ExtendedDriver) extends 
  FileTables with ProjectTables with UserTables with Profile with Mappers {
  
  import profile.simple._
  
  val tables = Seq(
    FileInfos,
    LoginInfos,
    OpenedFiles,
    ProjectAccessLevels,
    ProjectInfos,
    Revisions,
    SessionInfos,
    UserInfos)
   
  def create(implicit session: Session) {    
    tables.map(_.ddl).reduce(_++_).create
  }  
}