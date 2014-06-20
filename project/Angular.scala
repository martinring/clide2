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
import sbt.Keys._
import play._
import java.io.File
import java.io.FileReader
import scala.collection.SortedSet

/**
 * Provides some very pragmatic integration of angular.js into the play
 * framework
 *
 * @author Martin Ring
 */
object Angular extends AutoPlugin {
  override def requires = Play

  object autoImport {
    val angularModuleDirs = SettingKey[Map[String,(String,String,Boolean)]]("angular-module-directories")
    val angularOtherModules = SettingKey[Map[String,String]]("angular-other-modules")
    val angularConfigDir = SettingKey[String]("angular-config-directory")
  }

  import autoImport._

  override val projectSettings = Seq[Setting[_]](
    angularConfigDir := "config",
    angularOtherModules := Map(),
    angularModuleDirs := Map()
  )

  // (moduleName -> (path,name)*)*
  private val previous = scala.collection.mutable.Map[String,SortedSet[String]]()

  private def string(any: Any) = "'" + any.toString() + "'"

  val BoilerplateGenerator = (resourceManaged in Compile, sourceDirectory in Compile, name, version, angularModuleDirs, angularOtherModules, angularConfigDir) map { (outDir,sourceDir,appName,appVersion,angularModuleDirs,angularOtherModules,angularConfigDir) =>
    val bps = angularModuleDirs.map { case (what,(ngf,postfix,capitalize)) =>
      val inFiles = ((sourceDir / "assets" / "javascripts" / what) * "*.coffee").get
      val names = SortedSet(inFiles.map(_.getName.dropRight(7)) :_*)
      val outFile = outDir / "public" / "javascripts" / (what+".js")
      if (previous.get(what).map(_ != names).getOrElse(true)) {
        previous(what) = names
		    val builder = new StringBuilder("define([")
		    builder ++= names.map(file => "'"+what+"/"+file+"'").mkString(",")
		    builder ++= "],function("
		    builder ++= names.mkString(",")
		    builder ++= s"){var module=angular.module('$appName.$what',[]);"
		    builder ++= names.map(file => "module."+ngf+"('"+(if(capitalize)file.capitalize else file)+postfix+"',"+file+")").mkString(";")
		    builder ++= "})"
		    IO.write(outFile, builder.toString)
      }
      outFile
	  }
    val configs = SortedSet(((sourceDir /"assets"/"javascripts"/angularConfigDir) * "*.coffee").get.map(_.getName.dropRight(7)) :_*)
    val appFile = outDir / "public" / "javascripts" / "app.js"
    if (previous.get(angularConfigDir).map(_ != configs).getOrElse(true)) {
      previous(angularConfigDir) = configs
      val builder = new StringBuilder("define([")
	  builder ++= (configs.map(file=>string(angularConfigDir+"/"+file)).toSeq ++ angularModuleDirs.keys.map(string).toSeq).mkString(",")
      builder ++= "],function("
      builder ++= (configs.toSeq).mkString(",")
      builder ++= s"){var app=angular.module('$appName',["
      builder ++= (angularModuleDirs.keys.map(f=>"'"+appName+"."+f+"'") ++ angularOtherModules.values.map(f=>"'"+f+"'")).mkString(",")
      builder ++= "]);"
      builder ++= configs.map(f=>"app.config("+f+");").mkString
      builder ++= s"app.value('version','$appVersion');app.value('date',${System.currentTimeMillis});return app"
      builder ++= "})"
      IO.write(appFile, builder.toString)
    }
    Seq(appFile) ++ bps.toSeq
  }
}
