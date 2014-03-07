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
import scalajs.sbtplugin.ScalaJSPlugin._
import ScalaJSKeys._
import play.Project._

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

  private var commonSettings_ : Option[Seq[Setting[_]]] = None
  def commonSettings_=(settings: Seq[Setting[_]]) = 
    commonSettings_ = Some(settings)

  def module(suffix: String, name_suffix: String = "") = {
    val proj = Project(
      base = file(s"modules/clide-$suffix"),
      id = s"clide-$suffix$name_suffix"  
    ).settings(      
      name := s"clide-$suffix"
    )
    commonSettings_.foldLeft(proj)(_.settings(_ :_*))    
  }

  def playModule(suffix: String) = 
    module(suffix).settings(playScalaSettings:_*)

  def jsModule(suffix: String) =
    module(suffix,"-js").settings(scalaJSSettings:_*)
      .settings(target ~= (_ / "javascript"))

  def sharedModule(suffix: String) = 
    (module(suffix),jsModule(suffix))

  implicit class ScalaJSPlayProject(val project: Project) {
    def dependsOnJs(references: (Project,String)*): Project =
      references.foldLeft(project){ case (project,(ref,name)) =>
        project.settings (
          resourceGenerators in Compile <+= (preoptimizeJS in (ref,Compile), resourceManaged in Compile).map { (opt,outDir) =>
            val path = outDir / "public" / "javascripts" / name
            if (!path.exists || (path olderThan opt))
              IO.copyFile(opt, path, true)          
            Seq[java.io.File](path)
          },
          watchSources <++= watchSources in ref,
          playMonitoredFiles <<= (playMonitoredFiles, watchSources in ref).map { (files,refSources) =>
            (files ++ refSources.map(_.getCanonicalPath)).distinct
          }
        )
      }
  }
}