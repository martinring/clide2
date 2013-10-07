package clide

import play.api._
import clide.actors.Infrastructure

object Global extends GlobalSettings {    
  override def onStart(app: Application) {    
    import clide.actors._
    Logger.info("initializing actor infrastructure")    
    Infrastructure.initialize()
  }
  
  override def onStop(app: Application) {
    Infrastructure.shutdown()
  }
}