package clide.persistence

import scala.slick.session.Database

case class DBAccess(db: Database, schema: Schema)