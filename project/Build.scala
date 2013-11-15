 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

import sbt._
import Keys._
import play.Project._
import com.typesafe.sbt.SbtAtmos.{Atmos,atmosSettings}
import akka.sbt.AkkaKernelPlugin
import akka.sbt.AkkaKernelPlugin.{ Dist, outputDirectory, distJvmOptions}
import Dependencies._


object ApplicationBuild extends Build {
  val version = "2.0-SNAPSHOT"

  override def rootProject = Some(core)

  val commonSettings = Seq(
    scalaVersion := scala.version,
    scalacOptions ++= Seq("-encoding", "UTF-8", "-deprecation", "-unchecked", "-feature"))

  // Core
  // ===========================================================================

  val coreDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel,
    akka.testkit,
    spray.json,
    scala.reflect,
    slick,h2,slf4j,scalatest,scalacheck)

  val coreSettings =
    commonSettings ++
    AkkaKernelPlugin.distSettings ++
    atmosSettings ++ Seq(
      resolvers += spray.resolver,
      libraryDependencies ++= coreDependencies
    )


  val core = Project(
    id   = "clide-core",
    base = file("modules/clide-core"))
    .settings(coreSettings:_*)
    .configs(Atmos)

  // Web
  // ===========================================================================

  val webDependencies = Seq(
    akka.remote, playplugins.mailer)

  val webSettings = Angular.defaultSettings ++ Seq(
    scalaVersion := scala.version,
    //requireJs += "main.js",  TODO: This needs to be fixed to work again!
    //requireJsShim += "main.js",
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

  val web = play.Project(
    name = "clide-web",
    applicationVersion = version,
    dependencies = webDependencies,
    path = file("modules/clide-web"))
  .settings(webSettings:_*)
  .dependsOn(core)

  // ASSISTANTS
  // ===========================================================================

  val assistantDependencies = Seq(
    akka.actor, akka.remote, akka.kernel)

  // Isabelle Assistant
  // ---------------------------------------------------------------------------

  val isabelleDependencies = assistantDependencies ++ Seq(
    scala.swing,
    scala.actors)

  val isabelleSettings = commonSettings ++ Seq(
    libraryDependencies ++= isabelleDependencies)

  val isabelle = Project(
    id           = "clide-isabelle",
    base         = file("modules/clide-isabelle"),
    dependencies = Seq(core))
  .settings(isabelleSettings:_*)

  // Haskell Assistant
  // ---------------------------------------------------------------------------

  val haskellDependencies = assistantDependencies

  val haskellSettings = commonSettings ++ Seq(
    libraryDependencies ++= haskellDependencies)

  val haskell = Project(
    id           = "clide-haskell",
    base         = file("modules/clide-haskell"),
    dependencies = Seq(core))
  .settings(haskellSettings:_*)
}
