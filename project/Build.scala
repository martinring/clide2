import sbt._
import Keys._
import play.Project._

object ApplicationBuild extends Build {
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"

  val appDependencies = Seq(    
    "com.typesafe.akka"  %% "akka-testkit"        % "2.2.0"    % "test",
    "com.typesafe"       %% "play-plugins-mailer" % "2.1.0",
    "com.typesafe.play"  %% "play-slick"          % "0.5.0.2")

  override def rootProject = Some(main)

  val common = Project("clide-common", file("modules/clide-common"))

  val isabelle = Project("clide-isabelle", file("modules/clide-isabelle")).dependsOn(common)

  val main = play.Project(
    appName, 
    appVersion, 
    appDependencies,
    path = file("modules/clide-ui")
  ).settings(Angular.defaultSettings:_*).settings(
    scalaVersion := "2.10.2",    
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
  ).dependsOn(common)
}
