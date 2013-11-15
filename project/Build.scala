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
  val appName         = "clide"
  val appVersion      = "2.0-SNAPSHOT"

  override def rootProject = Some(bundle)

  val coreDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel,
    akka.testkit,
    spray.json,
    scala.reflect,
    slick,h2,slf4j,scalatest,scalacheck)

  val commonSettings = Seq(
    scalaVersion := scala.version,
    scalacOptions ++= Seq("-encoding", "UTF-8", "-deprecation", "-unchecked"),
    javacOptions  ++= Seq("-Xlint:unchecked", "-Xlint:deprecation"),
    resourceDirectory in Compile <<= baseDirectory / "conf",
    resourceDirectory in Test <<= baseDirectory / "conf",
    sourceDirectory in Compile <<= baseDirectory / "app",
    scalaSource in Compile <<= baseDirectory / "app",
    javaSource in Compile <<= baseDirectory / "app",
    sourceDirectory in Test <<= baseDirectory / "test",
    scalaSource in Test <<= baseDirectory / "test",
    javaSource in Test <<= baseDirectory / "test")

  val core = Project(s"${appName}-core", file("modules/clide-core"))
             .settings(commonSettings:_*).settings(AkkaKernelPlugin.distSettings:_*).settings(
    resolvers += spray.resolver,
    libraryDependencies ++= coreDependencies
  ).configs(Atmos).settings(atmosSettings:_*)

  val appDependencies = Seq(
    akka.remote,
    //scala.pickling, TODO
    playplugins.mailer)

  val web = play.Project(
    s"${appName}-web",
    appVersion,
    appDependencies,
    path = file("modules/clide-web")
  ).dependsOn(core).settings(Angular.defaultSettings:_*)
  .settings(
    // this is needed for scala pickling TODO: Fix
    // resolvers += Resolver.sonatypeRepo("snapshots"),
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

  val isabelleDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel,
    scala.swing,
    scala.actors)

  val isabelle = Project(s"${appName}-isabelle", file("modules/clide-isabelle"))
                .dependsOn(core).settings(commonSettings:_*).settings(
    libraryDependencies ++= isabelleDependencies
  )

  val ghcDependencies = Seq(
    akka.actor,
    akka.remote,
    akka.kernel)

  val ghc = Project(s"${appName}-ghc", file("modules/clide-ghc"))
            .dependsOn(core).settings(commonSettings:_*).settings(
    libraryDependencies ++= ghcDependencies
  )
}
