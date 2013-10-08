package clide.bundle

import play.api._


object Global extends GlobalSettings {  
  override def onStart(app: Application) {
    clide.Core.startup()    
    clide.plugins.Isabelle.startup()    
    clide.web.Global.onStart(app)
  }
  
  override def onStop(app: Application) {
    clide.Core.shutdown()
    clide.plugins.Isabelle.shutdown()
    clide.web.Global.onStop(app)
  }
}