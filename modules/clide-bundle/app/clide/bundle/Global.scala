package clide.bundle

import play.api._


object Global extends GlobalSettings {  
  override def onStart(app: Application) {
    clide.Core.startup()    
    clide.isabelle.Isabelle.startup()
    clide.web.Global.onStart(app)
  }
  
  override def onStop(app: Application) {
    clide.Core.shutdown()
    clide.isabelle.Isabelle.shutdown()
    clide.web.Global.onStop(app)
  }
}