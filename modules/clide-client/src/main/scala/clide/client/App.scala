package clide.client

import scala.scalajs.js
import scala.language.implicitConversions
import org.scalajs.dom._

trait ViewModel {
  trait Property[T]
  def Property[T] = new Property[T] { }
  def Property[T](initial: T) = new Property[T] { }
  def update[T](ref: Property[T], value: T)
  def apply[T](ref: Property[T]): T
}

object LoginViewModel extends ViewModel {
  val username = Property[String](localStorage.getItem("username").asInstanceOf[String])
  val login    = Property[String]
}

trait View[M <: ViewModel] {
  
}

object App {
  lazy val root = document.getElementById("root")  
  
  def startup() {
    LoginViewModel(LoginViewModel.username) = "Hallo"
    val x = LoginViewModel(LoginViewModel.login)    
  }
}