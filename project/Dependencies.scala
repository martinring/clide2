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

trait Dependencies {
  val slick = "com.typesafe.slick" %% "slick" % "1.0.1"
  val h2    = "com.h2database" % "h2" % "1.3.166"
  val slf4j = "org.slf4j" % "slf4j-nop" % "1.6.4"

  val jscala = "org.jscala" %% "jscala-macros" % "0.3-SNAPSHOT"

  val scalatest  = "org.scalatest" %% "scalatest" % "2.1.3" % "test"
  val scalacheck = "org.scalacheck" %% "scalacheck" % "1.11.3" % "test"
  val junit = "com.novocode" % "junit-interface" % "0.9" % "test"

  object akka {
    val version     = "2.3.3"
    val actor       = "com.typesafe.akka" %% "akka-actor"   % version
    val remote      = "com.typesafe.akka" %% "akka-remote"  % version
    val kernel      = "com.typesafe.akka" %% "akka-kernel"  % version
    val persistence = "com.typesafe.akka" %% "akka-persistence-experimental"  % version
    val testkit     = "com.typesafe.akka" %% "akka-testkit" % version % "test"
  }

  object spray {
    val resolver = "spray" at "http://repo.spray.io/"
    val json     = "io.spray" %% "spray-json" % "1.2.5"
  }

  object scala {
    val version  = "2.10.4"
    def compiler(version: String) = "org.scala-lang" % "scala-compiler" % version
    val swing    = "org.scala-lang" % "scala-swing"   % version
    val actors   = "org.scala-lang" % "scala-actors"  % version
    val reflect  = "org.scala-lang" % "scala-reflect" % version
    val quasiquotes = "org.scalamacros" % "quasiquotes" % "2.0.0-M3" cross CrossVersion.full
  }

  object playplugins {
    val slick   = "com.typesafe.play" %% "play-slick"          % "0.5.0.2"
    val mailer  = "com.typesafe"      %% "play-plugins-mailer" % "2.1.0"
  }

  object scalajs {
    val dom          = "org.scala-lang.modules.scalajs" %% "scalajs-dom" % "0.3"
    val playPickling = "org.scalajs" %% "scalajs-pickling-play-json" % "0.2"
    val pickling     = "org.scalajs" %% "scalajs-pickling" % "0.2"
  }

  implicit class DependenciesProject(project: Project) {
    def dependsOn(deps: ModuleID*) =
      project.settings(libraryDependencies ++= deps)

    def dependsOnSrc(deps: Project*) =
      deps.foldLeft(project) { case (p,d) => p.settings(
        unmanagedSourceDirectories in Compile += (sourceDirectory in d).value
      )}
  }
}

