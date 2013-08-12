package controllers

import play.api.mvc._
import play.api.db.slick.DB.withSession
import play.api.Play.current

object Projects extends Controller with Secured {
  def index = IsAuthenticated { user => implicit request => withSession { implicit session =>
    Ok(models.Projects.getForUser(user).elements.mkString)
  } }
}