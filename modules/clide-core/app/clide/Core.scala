package clide

import akka.actor._
import com.typesafe.config.ConfigFactory
import akka.kernel.Bootable
import clide.actors.UserServer
import scala.slick.session.Database
import scala.reflect.runtime.universe
import scala.slick.driver.ExtendedDriver
import clide.persistence.DAL
import scala.slick.session.Session

object Core extends Bootable {
  val system   = ActorSystem("clide",ConfigFactory.load.getConfig("clide"))
  val config   = system.settings.config
  
  val profile = {
    val runtimeMirror = universe.runtimeMirror(getClass.getClassLoader)
    val module = runtimeMirror.staticModule(config.getString("db.profile"))    
    runtimeMirror.reflectModule(module).instance.asInstanceOf[ExtendedDriver]      
  }
  
  lazy val DAL = new DAL(profile)    

  lazy val DB = slick.session.Database.forURL(   
    url      = config.getString("db.url"),
    user     = config.getString("db.user"),
    password = config.getString("db.password"),
    driver   = config.getString("db.driver"))
    
  def startup() {        
    val server = Some(system.actorOf(Props[UserServer], "users"))
  }
  
  def shutdown() {
    system.shutdown()
  }
}

object CoreApp extends App {
  Core.startup()
  readLine()
  Core.shutdown()
}