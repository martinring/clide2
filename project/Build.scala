import sbt._
import Keys._
import play.Project._
import scala.collection.mutable.StringBuilder

object ApplicationBuild extends Build with Angular {
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"   
    
  val appDependencies = Seq(
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "com.typesafe" %% "play-plugins-mailer" % "2.1.0",
    "com.typesafe.akka" %% "akka-testkit"  % "2.2.0"% "test",
    "com.typesafe.play" %% "play-slick" % "0.3.2",
    "com.typesafe.slick" %% "slick" % "1.0.0",           
    "org.webjars" % "angularjs" % "1.2.0rc1",
    "org.webjars" % "codemirror" % "3.16",
    "org.webjars" % "jquery" % "2.0.3",
    "org.webjars" % "marked" % "0.2.9",
    "org.webjars" % "requirejs" % "2.1.1",
    "org.webjars" % "underscorejs" % "1.5.1",
    "org.webjars" % "webjars-play" % "2.1.0-1",    
    jdbc
  )
    
  val main = play.Project(appName, appVersion, appDependencies).settings(ngDefaultSettings:_*).settings(    
    scalaVersion := "2.10.2",
    resolvers += Resolver.url("Objectify Play Repository", url("http://schaloner.github.com/releases/"))(Resolver.ivyStylePatterns),
    resolvers += Resolver.url("Objectify Play Snapshot Repository", url("http://schaloner.github.com/snapshots/"))(Resolver.ivyStylePatterns),    
    lessEntryPoints <<= baseDirectory(d => (d / "app" / "assets" / "stylesheets" ** "main.less")),
    requireJs += "main.js",
    requireJsShim += "main.js",
    ngOtherModules ++= Map(
        "angular-cookies" -> "ngCookies",
        "angular-route" -> "ngRoute"),
    ngModuleDirs ++= Map(
        "services" -> ("service","",true),
        "directives" -> ("directive","",false),
        "filters" -> ("filter","",false),
        "controllers" -> ("controller", "Controller", true)),    
    resourceGenerators in Compile <+= ngBoilerplateGenerator,
    resourceGenerators in Compile <+= LessCompiler,
    resourceGenerators in Compile <+= ngModuleCompiler
  )
}
