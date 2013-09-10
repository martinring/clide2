import sbt._
import Keys._
import play.Project._
import scala.collection.mutable.StringBuilder

object ApplicationBuild extends Build {
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"
  val appDependencies = Seq(    
    "com.typesafe.akka"  %% "akka-testkit"        % "2.2.1" % "test",
    "com.typesafe"       %% "play-plugins-mailer" % "2.1.0",
    "com.typesafe.play"  %% "play-slick"          % "0.5.0.3")
    
  val main = play.Project(appName, appVersion, appDependencies).settings(Angular.defaultSettings:_*).settings(    
    scalaVersion := "2.10.2",    
    lessEntryPoints <<= (sourceDirectory in Compile)(base => base / "assets" / "stylesheets" ** "main.less"),
    requireJs += "main.js",
    requireJsShim += "main.js",
    Angular.otherModules ++= Map(
        "angular-animate"  -> "ngAnimate",
        "angular-cookies"  -> "ngCookies",
        "angular-route"    -> "ngRoute",
        "angular-resource" -> "ngResource"),
    Angular.moduleDirs ++= Map(
        "controllers" -> ("controller", "Controller", true),
        "directives" -> ("directive","",false),
        "filters" -> ("filter","",false),
        "services" -> ("service","",true)),
    resourceGenerators in Compile <+= LessCompiler,
    resourceGenerators in Compile <+= Angular.ModuleCompiler,
    resourceGenerators in Compile <+= Angular.BoilerplateGenerator
  )
}
