import sbt._
import Keys._
import play.Project._

object ApplicationBuild extends Build {
  val appName         = "clide2"
  val appVersion      = "1.0-SNAPSHOT"   

  val appDependencies = Seq(    
    "com.typesafe.slick" %% "slick" % "1.0.0",
    "com.typesafe.play" %% "play-slick" % "0.3.2",   
    "com.typesafe" %% "play-plugins-mailer" % "2.1.0",
    "org.webjars" % "angularjs" % "1.1.5-1",
    "org.webjars" % "codemirror" % "3.13",
    "org.webjars" % "jquery" % "2.0.2",   
    "org.webjars" % "requirejs-plugins" % "3ff54566f8",
    "org.webjars" % "webjars-play" % "2.1.0-1",
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "com.typesafe.akka" %% "akka-testkit"  % "2.2.0"% "test",
    jdbc
  )

  val main = play.Project(appName, appVersion, appDependencies).settings(    
    scalaVersion := "2.10.2",
    resolvers += Resolver.url("Objectify Play Repository", url("http://schaloner.github.com/releases/"))(Resolver.ivyStylePatterns),
    resolvers += Resolver.url("Objectify Play Snapshot Repository", url("http://schaloner.github.com/snapshots/"))(Resolver.ivyStylePatterns),    
    lessEntryPoints <<= baseDirectory(d => (d / "app" / "assets" / "stylesheets" ** "main.less")),
    requireJs += "main.js",
    requireJsShim += "main.js"
  ) //dependsOn RootProject(file("../play-js"))
}
