package clide.web.controllers

import play.api.mvc._
import play.api.libs.json._

object Backstage extends Controller with ActorAsk {
  def session(user: String) = WebSocket.async[JsValue] {
    null
  }
}