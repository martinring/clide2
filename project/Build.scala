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
import akka.sbt.AkkaKernelPlugin.{ Dist, outputDirectory, distJvmOptions}
import Dependencies._


object ApplicationBuild extends Build {
  val v = "2.0-SNAPSHOT"

  override def rootProject = Some(core)

  val sonatypeSettings = Seq(
    organization := "net.flatmap",
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
    licenses := Seq("GNU General Public License" -> url("http://www.gnu.org/licenses/lgpl.html")),
    homepage := Some(url("http://clide.flatmap.net")),
    pomExtra := (
      <scm>
        <url>git@github.com:martinring/clide2.git</url>
        <connection>scm:git:git@github.com:martinring/clide2.git</connection>
      </scm>
      <developers>
        <developer>
          <id>martinring</id>
          <name>Martin Ring</name>
          <url>http://gihub.com/martinring</url>
        </developer>
      </developers>),
    publishArtifact in Test := false)

  val commonSettings = sonatypeSettings ++ Seq(
    version := v,
    scalaVersion := scala.version,
    scalacOptions ++= Seq("-encoding", "UTF-8", "-deprecation", "-unchecked", "-feature"))

  // Core
  // ===========================================================================

  val coreDependencies = Seq(
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

  // Web
  // ===========================================================================

  val webDependencies = Seq(jscala,
    akka.remote, playplugins.mailer)

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
