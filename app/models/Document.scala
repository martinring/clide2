package models

import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}

class Document (id: Long, folder: Long, name: String, content: String)
