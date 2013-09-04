import sbt._
import Keys._
import play.Project._
import scala.collection.mutable.StringBuilder
import com.typesafe.sbt.SbtAtmos.{ Atmos, atmosSettings }

object ApplicationBuild extends Build {
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"
  val appDependencies = Seq(
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "com.typesafe" %% "play-plugins-mailer" % "2.1.0",
    "com.typesafe.akka" %% "akka-testkit"  % "2.2.0"% "test",
    "com.typesafe.play" %% "play-slick" % "0.5.0.3",
    "com.typesafe.slick" %% "slick" % "1.0.1",
    "org.webjars" % "angularjs" % "1.1.5-1",
    "org.webjars" % "codemirror" % "3.16",
    "org.webjars" % "font-awesome" % "3.2.1",
    "org.webjars" % "jquery" % "2.0.3",
    "org.webjars" % "marked" % "0.2.9",
    "org.webjars" % "requirejs" % "2.1.1",
    "org.webjars" % "underscorejs" % "1.5.1",
    "org.webjars" % "webjars-play" % "2.1.0-1",
    jdbc
  )
    
  val main = play.Project(appName, appVersion, appDependencies).settings(Angular.defaultSettings:_*).settings(    
    scalaVersion := "2.10.2",
    resolvers += Resolver.url("Objectify Play Repository", url("http://schaloner.github.com/releases/"))(Resolver.ivyStylePatterns),
    resolvers += Resolver.url("Objectify Play Snapshot Repository", url("http://schaloner.github.com/snapshots/"))(Resolver.ivyStylePatterns),
    lessEntryPoints <<= baseDirectory(d => (d / "app" / "assets" / "stylesheets" ** "main.less")),
    requireJs += "main.js",
    requireJsShim += "main.js",
    Angular.otherModules ++= Map(
        //"angular-animate" -> "ngAnimate",
        "angular-cookies" -> "ngCookies"),
        //"angular-route" -> "ngRoute",
        //"angular-resource" -> "ngResource"),
    Angular.moduleDirs ++= Map(
        "controllers" -> ("controller", "Controller", true),
        "directives" -> ("directive","",false),
        "filters" -> ("filter","",false),
        "services" -> ("service","",true)),
    resourceGenerators in Compile <+= LessCompiler,
    resourceGenerators in Compile <+= Angular.ModuleCompiler,
    resourceGenerators in Compile <+= Angular.BoilerplateGenerator
  ).settings(atmosSettings: _*)
}
