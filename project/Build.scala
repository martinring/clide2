import sbt._
import Keys._
import play.Project._
import Dependencies._
import com.typesafe.sbt.SbtAtmos.{Atmos,atmosSettings}
import com.typesafe.sbt.SbtAtmosPlay.atmosPlaySettings

object ApplicationBuild extends Build {
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"

  override def rootProject = Some(web)

  val coreDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel,
    scala.reflect,
    slick,h2,slf4j)

  val commonSettings = Seq(
    scalaVersion      := scala.version,
    resourceDirectory in Compile <<= baseDirectory / "conf",
    resourceDirectory in Test <<= baseDirectory / "conf",
    sourceDirectory in Compile <<= baseDirectory / "app",
    scalaSource in Compile <<= baseDirectory / "app",
    javaSource in Compile <<= baseDirectory / "app",
    sourceDirectory in Test <<= baseDirectory / "test",
    scalaSource in Test <<= baseDirectory / "test",
    javaSource in Test <<= baseDirectory / "test")

  val core = Project(s"${appName}-core", file("modules/clide-core"))
             .settings(commonSettings:_*).settings(    
    libraryDependencies ++= coreDependencies
  )

  val appDependencies = Seq(
    akka.testkit,
    akka.remote,
    playplugins.slick,
    playplugins.mailer)
  
  val web = play.Project(
    s"${appName}-web", 
    appVersion, 
    appDependencies,
    path = file("modules/clide-web")
  ).dependsOn(core).settings(Angular.defaultSettings:_*)  
  .settings(atmosPlaySettings: _*)
  .settings(
    scalaVersion := scala.version,
    resolvers += Resolver.url("github repo for play-slick",
      url("https://raw.github.com/loicdescotte/loicdescotte.github.com/master/releases/"))
      (Resolver.ivyStylePatterns),
    requireJs += "main.js",
    requireJsShim += "main.js",
    Angular.otherModules ++= Map(
        "angular-animate"  -> "ngAnimate",
        "angular-cookies"  -> "ngCookies",
        "angular-route"    -> "ngRoute",
        "angular-resource" -> "ngResource",
        "ui-bootstrap"     -> "ui.bootstrap"),
    Angular.moduleDirs ++= Map(
        "controllers" -> ("controller", "Controller", true),
        "directives"  -> ("directive","",false),
        "filters"     -> ("filter","",false),
        "services"    -> ("service","",true)),
    resourceGenerators in Compile <+= LessCompiler,
    resourceGenerators in Compile <+= JavascriptCompiler(fullCompilerOptions = None),
    resourceGenerators in Compile <+= Angular.ModuleCompiler,
    resourceGenerators in Compile <+= Angular.BoilerplateGenerator,
    lessEntryPoints         <<= (sourceDirectory in Compile){ base => 
      base / "assets" / "stylesheets" * "main.less" },
    coffeescriptEntryPoints <<= (sourceDirectory in Compile){ base => 
      base / "assets" ** "*.coffee" },
    javascriptEntryPoints <<= (sourceDirectory in Compile){ base => 
      (base / "assets" ** "*.js") --- 
      (base / "assets" / "libs" / "bootstrap" / "assets" ** "*") --- 
      (base / "assets" / "libs" / "bootstrap" / "js" / "tests" ** "*") --- 
      (base / "assets" / "libs" / "codemirror" / "test" ** "*") }
  )

  val isabelleDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel,
    scala.swing,
    scala.actors)    

  val isabelle = Project(s"${appName}-isabelle", file("modules/clide-isabelle"))
                .dependsOn(core).settings(
    scalaVersion := scala.version,
    libraryDependencies ++= isabelleDependencies
  ).configs(Atmos).settings(atmosSettings: _*)
}
