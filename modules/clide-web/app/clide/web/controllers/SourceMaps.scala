package clide.web.controllers

import play.api.Play.current
import play.api._
import play.api.libs.iteratee.Enumerator
import play.api.mvc._
import scala.concurrent.ExecutionContext.Implicits.global
import java.io.File
 
object SourceMaps extends Controller {
  def scalaFile(module: String, path: String) = Action { request =>
    val absPath = Play.current.path.getParent() + request.path
    val file = new File(absPath)
    if (file.exists())
        Ok.chunked(Enumerator.fromFile(file))
    else
      NotFound(s"File ${request.path} not found")    
  }
}