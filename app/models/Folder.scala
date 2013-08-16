package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

case class Folder(id: Long, name: String, )

object Folders extends Table[Folder]("folders") {
  
}