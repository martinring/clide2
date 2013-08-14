package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

class Document (id: Long, folderId: Long, name: String, content: String)
