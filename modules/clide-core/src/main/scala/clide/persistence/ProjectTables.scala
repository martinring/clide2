package clide.persistence

import clide.models._
import scala.slick.lifted.ForeignKeyAction

trait ProjectTables { this: Profile with Mappers with UserTables =>
  import profile.simple._ 
  
  object Projects extends Table[(String,String,Option[String])]("PROJECTS") {
    def id           = column[Long]("id", O.PrimaryKey, O.AutoInc)
    def ownerName    = column[String]("OWNER")
	def name         = column[String]("NAME")				
	def description  = column[Option[String]]("DESCRIPTION")
	def pk           = primaryKey("PK_PROJECT", (ownerName,name))		
	def owner        = foreignKey("FK_PROJECT_USER", ownerName, Users)(_.name, 
	    onUpdate = ForeignKeyAction.Cascade, 
	    onDelete = ForeignKeyAction.Cascade)
	def *            = ownerName ~ name ~ description
  }    
  
  object AccessLevels extends Table[(String,String,String,AccessLevel.Value)]("ACCESS_LEVELS") {
    def userName     = column[String]("USER")
    def projectOwner = column[String]("OWNER")
    def projectName  = column[String]("NAME")
    def level        = column[AccessLevel.Value]("LEVEL")
    def project   = foreignKey("FK_ACCESS_LEVEL_PROJECT", projectOwner ~ projectName, Projects)(p => p.ownerName ~ p.name, 
      onUpdate = ForeignKeyAction.Cascade,
      onDelete = ForeignKeyAction.Cascade)
    def user      = foreignKey("FK_ACCESS_LEVEL_USER", userName, Users)(_.name,
      onUpdate = ForeignKeyAction.Cascade,
      onDelete = ForeignKeyAction.Cascade)
    def pk        = primaryKey("PK_ACCESS_LEVEL", (projectOwner,projectName,userName))
    def * = userName ~ projectOwner ~ projectName ~ level
  }
}