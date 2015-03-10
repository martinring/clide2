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
import org.scalajs.sbtplugin._

trait BuildUtils {
  case class Developer(id: String, name: String, url: URL)

  def Developers(devs: Developer*) =
    <developers>
      { for (dev <- devs) yield
        <developer>
          <id>{dev.id}</id>
          <name>{dev.name}</name>
          <url>{dev.url}</url>
        </developer>
      }
    </developers>

  def baseName: String

  def commonSettings: Seq[Setting[_]]

  def module(suffix: String, idsuffix: String = "") = Project(
    base = file(s"modules/$baseName-$suffix"),
    id = s"$baseName-$suffix$idsuffix"
  ).settings(
    name := s"$baseName-$suffix"
  ).settings(
    commonSettings :_*
  )

  def playModule(suffix: String) = Project(
    base = file(s"modules/$baseName-$suffix"),
    id = s"$baseName-$suffix"
  ).enablePlugins(play.PlayScala)
   .settings(
    name := s"$baseName-$suffix"
  ).settings(
    commonSettings :_*
  )

  def jsModule(suffix: String) =
    module(suffix,"-js").enablePlugins(ScalaJSPlugin)
      .settings(target ~= (_ / "javascript"))

  def sharedModule(suffix: String) =
    (module(suffix),jsModule(suffix))

  implicit class SharedProject(val projects: (Project,Project)) {
    private val (jvmp,jsp) = projects
    def settings(ss: Def.Setting[_]*) = {
      (jvmp.settings(ss :_*),jsp.settings(ss :_*))
    }
    def jvm(f: Project => Project) = (f(jvmp),jsp)
    def js(f: Project => Project) = (jvmp,f(jsp))
    def dependsOn(references: ModuleID*) = settings(libraryDependencies ++= references)
  }

  /*implicit class ScalaJSPlayProject(val project: Project) {
    def dependsOnJs(references: (Project,String)*): Project =
      references.foldLeft(project){ case (project,(ref,name)) =>
        project.settings (
          scalajsOutputDir     := (crossTarget in Compile).value / "classes" / "public" / "javascripts",
          compile in Compile <<= (compile in Compile) dependsOn (preoptimizeJS in (project, Compile)),
          dist <<= dist dependsOn (optimizeJS in (project, Compile)),
          unmanagedSourceDirectories in Compile += new File((baseDirectory.value / ".." / sharedSrcDir).getCanonicalPath)
        )
      }
  }*/
}
