/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
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
import play.Play._
import scala.scalajs.sbtplugin.ScalaJSPlugin._
import ScalaJSKeys._
import com.typesafe.sbt.packager.universal.UniversalKeys
import com.typesafe.sbteclipse.core.EclipsePlugin.EclipseKeys

object ClideBuild extends Build with BuildUtils with Publishing with Dependencies with UniversalKeys {
  override def rootProject = Some(web)

  val baseName = "clide"

  val commonSettings = sonatypeSettings ++ Seq(
    version := "2.0-SNAPSHOT",
    organization := "net.flatmap",
    organizationName := "flatmap",
    organizationHomepage := Some(url("http://www.flatmap.net")),
    startYear := Some(2012),
    licenses := Seq("GNU Lesser General Public License" -> url("http://www.gnu.org/licenses/lgpl.html")),
    homepage := Some(url("http://clide.flatmap.net")),
    scmInfo := Some(ScmInfo(
      browseUrl = url("https://github.com/martinring/clide2"),
      connection = "scm:git:git@github.com:martinring/clide2.git")),
    scalaVersion := scala.version,
    scalacOptions ++= Seq("-encoding", "UTF-8", "-deprecation", "-unchecked", "-feature"),
    pomExtra := Developers(
    Developer("martinring", "Martin Ring", url("http://github.com/martinring")))
  )

  lazy val (collaboration,collaborationJs) = sharedModule("collaboration")

  lazy val (common,commonJs) = sharedModule("common")

  lazy val xml = module("xml").dependsOn(scala.reflect, scala.xml)

  lazy val core = module("core")
    .dependsOn(collaboration,common)
    .dependsOn(
      "ch.qos.logback" % "logback-classic" % "1.0.13", spray.json,
      akka.actor, akka.remote, akka.kernel, akka.testkit,
      akka.persistence, scala.reflect, slick,h2,scalatest,scalacheck)

  lazy val (reactive,reactiveJs) = sharedModule("reactive").dependsOn(scalatest,scalacheck,junit)

  lazy val reactiveUi = jsModule("reactive-ui").dependsOn(reactiveJs).settings(
    libraryDependencies += "org.scala-lang.modules.scalajs" %%% "scalajs-dom" % "0.6")

  lazy val client = jsModule("client")
    .settings(
      libraryDependencies += "org.scala-lang.modules.scalajs" %%% "scalajs-dom" % "0.6",
      libraryDependencies += "com.greencatsoft" %%% "scalajs-angular" % "0.1",
      libraryDependencies += "com.lihaoyi" %%% "upickle" % "0.2.5",
      persistLauncher := true,
      persistLauncher in Test := true,
      relativeSourceMaps := true
    ).dependsOn(xml, reactiveUi, collaborationJs, commonJs)

  lazy val web = playModule("web").enablePlugins(Angular)
    .dependsOn(core,common)
    .settings(
      Angular.autoImport.angularOtherModules ++= Map(
        "angular-animate"  -> "ngAnimate",
        "angular-cookies"  -> "ngCookies",
        "angular-route"    -> "ngRoute",
        "angular-resource" -> "ngResource",
        "ui-bootstrap"     -> "ui.bootstrap"),
      Angular.autoImport.angularModuleDirs ++= Map(
          "controllers" -> ("controller", "Controller", true),
          "directives"  -> ("directive","",false),
          "filters"     -> ("filter","",false),
          "services"    -> ("service","",true)),
      resourceGenerators in Compile <+= Angular.BoilerplateGenerator,
      play.PlayImport.PlayKeys.lessEntryPoints <<= (sourceDirectory in Compile){ base =>
        base / "assets" / "stylesheets" * "main.less" },
      compile in Compile <<= (compile in Compile) dependsOn (fastOptJS in (client, Compile)) dependsOn copySourceMapsTask,
      dist <<= dist dependsOn (fullOptJS in (client, Compile)),
      stage <<= stage dependsOn (fullOptJS in (client, Compile)),
      libraryDependencies += "com.lihaoyi" %% "upickle" % "0.2.5",
      crossTarget in (client, Compile, packageLauncher) := (classDirectory in Compile).value / "public" / "javascripts",
      crossTarget in (client, Compile, fastOptJS) := (classDirectory in Compile).value / "public" / "javascripts",
      crossTarget in (client, Compile, fullOptJS) := (classDirectory in Compile).value / "public" / "javascripts"
    )

  val copySourceMapsTask = Def.task {
    val scalaFiles = (Seq(client.base) ** ("*.scala")).get
    for (scalaFile <- scalaFiles) {
      val target = new File((classDirectory in Compile).value, scalaFile.getPath)
      IO.copyFile(scalaFile, target)
    }
  }

  // ASSISTANTS
  // ===========================================================================

  lazy val isabelle = module("isabelle")
    .dependsOn(core)
    .dependsOn(akka.actor, akka.remote, akka.kernel, scala.parsers)

  lazy val haskell = module("haskell")
    .dependsOn(core)
    .dependsOn(akka.actor, akka.remote, akka.kernel)

  lazy val scalaAssistant = module("scala")
    .dependsOn(core)
    .dependsOn(akka.actor, akka.remote, akka.kernel, scala.compiler(scala.version), "org.scala-refactoring" %% "org.scala-refactoring.library" % "0.6.2")

  lazy val spec = module("spec")
    .dependsOn(core)
    .dependsOn(akka.actor, akka.remote, akka.kernel)
}
