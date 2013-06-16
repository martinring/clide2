import sbt._
import Keys._
import play.Project._

object ApplicationBuild extends Build {

  val appName         = "clide2"
  val appVersion      = "1.0-SNAPSHOT"

  val appDependencies = Seq(    
    "com.typesafe.slick" %% "slick" % "1.0.0",
    "com.typesafe.play" %% "play-slick" % "0.3.2",
    jdbc
  )

  val main = play.Project(appName, appVersion, appDependencies).settings(
    lessEntryPoints <<= baseDirectory(d => (d / "app" / "assets" / "stylesheets" ** "main.less")),
    requireJs += "config.js",
    requireJsShim += "config.js"
  )
}
