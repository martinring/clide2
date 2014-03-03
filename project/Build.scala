/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

import sbt._
import Keys._
import play.Project._
import com.typesafe.sbt.SbtAtmos.{Atmos,atmosSettings}
import akka.sbt.AkkaKernelPlugin
import akka.sbt.AkkaKernelPlugin.{ Dist, outputDirectory, distJvmOptions, distMainClass }
import Dependencies._
import Util._
import scalajs.sbtplugin.ScalaJSPlugin._


object ApplicationBuild extends Build {
  val v = "2.0-SNAPSHOT"

  override def rootProject = Some(web)

  val sonatypeSettings = Seq(
    publishMavenStyle := true,
    publishTo := {
      val nexus = "https://oss.sonatype.org/"
      if (v.trim.endsWith("SNAPSHOT"))
        Some("snapshots" at nexus + "content/repositories/snapshots")
      else
        Some("releases" at nexus + "service/local/staging/deploy/maven2")
    },
    // To publish on maven-central, all required artifacts must also be hosted on maven central.
    // So we remove special repos from the pom
    //pomIncludeRepository := { _ => false },
    pomExtra := Developers(
      Developer("martinring", "Martin Ring", url("http://github.com/martinring"))),
    publishArtifact in Test := false)

  val commonSettings = sonatypeSettings ++ Seq(
    version := v,
    organization := "net.flatmap",
    organizationName := "flatmap",
    organizationHomepage := Some(url("http://www.flatmap.net")),
    parallelExecution in Test := false,
    startYear := Some(2012),
    licenses := Seq("GNU Lesser General Public License" -> url("http://www.gnu.org/licenses/lgpl.html")),
    homepage := Some(url("http://clide.flatmap.net")),
    scmInfo := Some(ScmInfo(
      browseUrl = url("https://github.com/martinring/clide2"),
      connection = "scm:git:git@github.com:martinring/clide2.git")),
    scalaVersion := scala.version,
    scalacOptions ++= Seq("-encoding", "UTF-8", "-deprecation", "-unchecked", "-feature"))

  // Collaboration
  // ===========================================================================

  val collaborationDependencies = Seq.empty

  val collaborationSettings = commonSettings

  val collaboration = Project(
    id   = "clide-collaboration",
    base = file("modules/clide-collaboration"))
    .settings(collaborationSettings:_*)

  // Messages
  // ===========================================================================

  val messagesDependencies = Seq(
    "org.scalajs" %% "scalajs-pickling-play-json" % "0.1-SNAPSHOT")

  val messagesSettings = commonSettings ++ Seq (
    libraryDependencies ++= messagesDependencies)

  val messages = Project(
    id = "clide-messages",
    base = file("modules/clide-messages"))
    .settings(messagesSettings:_*)

  // Core
  // ===========================================================================

  val coreDependencies = Seq(
    "ch.qos.logback" % "logback-classic" % "1.0.13",

    akka.actor, akka.remote, akka.kernel, akka.testkit,
    spray.json, scala.reflect,
    slick,h2,slf4j,scalatest,scalacheck)

  val coreSettings =
    commonSettings ++
    AkkaKernelPlugin.distSettings ++
    atmosSettings ++ Seq(
      resolvers += Resolver.sonatypeRepo("snapshots"),
      resolvers += spray.resolver,
      libraryDependencies ++= coreDependencies
    )


  val core = Project(
    id   = "clide-core",
    base = file("modules/clide-core"))
    .settings(coreSettings:_*)
    .configs(Atmos)
    .dependsOn(collaboration,messages)

  // Reactive
  // ===========================================================================

  val reactiveDependencies = Seq(
    "org.scalajs" %% "scalajs-actors" % "0.1-SNAPSHOT",
    "org.scala-lang.modules.scalajs" %% "scalajs-dom" % "0.1-SNAPSHOT")

  val reactiveSettings =
    commonSettings ++
    scalaJSSettings ++ Seq(
      libraryDependencies ++= reactiveDependencies)

  val reactive = Project(
    id = "clide-reactive",
    base = file("modules/clide-reactive"))
    .settings(reactiveSettings:_*)


  // Web - Client
  // ===========================================================================

  val clientDependencies = Seq(
    "org.scalajs" %% "scalajs-pickling" % "0.1-SNAPSHOT",
    "org.scala-lang.modules.scalajs" %% "scalajs-dom" % "0.1-SNAPSHOT")

  val clientSettings =
    commonSettings ++
    scalaJSSettings ++ Seq(
      libraryDependencies ++= clientDependencies,
      unmanagedSourceDirectories in Compile += (sourceDirectory in collaboration).value,
      //unmanagedSourceDirectories in Compile += (sourceDirectory in reactive).value,
      unmanagedSourceDirectories in Compile += (sourceDirectory in messages).value)

  val client = Project(
    id = "clide-client",
    base = file("modules/clide-client"))
    .settings(clientSettings:_*)
    .dependsOn(reactive)

  // Web - Server
  // ===========================================================================

  val webDependencies = Seq(
    "org.scalajs" %% "scalajs-pickling-play-json" % "0.1-SNAPSHOT")

  val webSettings = Angular.defaultSettings ++ commonSettings ++ Seq(
    resolvers += Resolver.sonatypeRepo("snapshots"),
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
    lessEntryPoints <<= (sourceDirectory in Compile){ base =>
      base / "assets" / "stylesheets" * "main.less" }
  )

  val web = play.Project(
    name = "clide-web",
    applicationVersion = v,
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

  val isabelleSettings = commonSettings ++ AkkaKernelPlugin.distSettings ++ Seq(
    distJvmOptions in Dist := "-Xms512M -Xmx1024M",
    distMainClass := "clide.isabelle.Isabelle",
    libraryDependencies ++= isabelleDependencies)

  val isabelle = Project(
    id           = "clide-isabelle",
    base         = file("modules/clide-isabelle"),
    dependencies = Seq(core))
  .settings(isabelleSettings:_*)

  // Haskell Assistant
  // ---------------------------------------------------------------------------

  val haskellDependencies = assistantDependencies

  val haskellSettings = commonSettings ++ AkkaKernelPlugin.distSettings ++ Seq(
    libraryDependencies ++= haskellDependencies)

  val haskell = Project(
    id           = "clide-haskell",
    base         = file("modules/clide-haskell"),
    dependencies = Seq(core))
  .settings(haskellSettings:_*)
}
