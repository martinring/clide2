import sbt._
import PlayProject._
import Keys._
import java.io.File
import scala.collection.SortedSet

object Angular {
  val moduleDirs = scala.collection.mutable.Map[String,(String,String,Boolean)]()
  val otherModules = scala.collection.mutable.Map[String,String]()
  var configDir: String = "config"
    
  private val previous = scala.collection.mutable.Map[String,SortedSet[String]]()
  
  val settings = Seq(moduleDirs,otherModules)
  
  val boilerplateGenerator = (resourceManaged in Compile, sourceDirectory in Compile, cacheDirectory, name) map { (outDir,sourceDir,cache,appName) =>         
    val dirs = moduleDirs
    val mods = otherModules    
    val bps = dirs.map { case (what,(ngf,postfix,capitalize)) =>
      val inFiles = ((sourceDir / "assets" / "javascripts" / what) * "*.coffee").get
      val names = SortedSet(inFiles.map(_.getName.dropRight(7)) :_*)
      val outFile = outDir / "public" / "javascripts" / (what+".js")
      if (previous.get(what).map(_ != names).getOrElse(true)) {
        println("boilerplate for " + what)
        previous(what) = names			 
		val builder = new StringBuilder("define(['angular'")
		builder ++= names.map(file => ",'"+what+"/"+file+"'").mkString
		builder ++= "],function(angular"
		builder ++= names.map(f=>","+f).mkString
		builder ++= "){var module=angular.module('"+appName+"."+what+"',[]);"
		builder ++= names.map(file => "module."+ngf+"('"+(if(capitalize)file.capitalize else file)+postfix+"',"+file+")").mkString(";")
		builder ++= "})"	
		IO.write(outFile, builder.toString)
      } 
      outFile
	}    
    val configs = SortedSet(((sourceDir /"assets"/"javascripts"/configDir) * "*.coffee").get.map(_.getName.dropRight(7)) :_*)
    val appFile = outDir / "public" / "javascripts" / "app.js"
    if (previous.get(configDir).map(_ != configs).getOrElse(true)) {
      println("boilerplate for app")
      previous(configDir) = configs
      val builder = new StringBuilder("define(['angular'")
  	  builder ++= configs.map(file => ",'"+configDir+"/"+file+"'").mkString    
      builder ++= mods.keys.map(file => ",'"+file+"'").mkString
      builder ++= dirs.keys.map(file => ",'"+file+"'").mkString 
      builder ++= "],function(angular,"
      builder ++= configs.mkString(",")
      builder ++= "){var app=angular.module('"+appName+"',["
      builder ++= (dirs.keys.map(f=>"'clide."+f+"'") ++ mods.values.map(f=>"'"+f+"'")).mkString(",") 
      builder ++= "]);"
      builder ++= configs.map(f=>"app.config("+f+");").mkString
      builder ++= "})"      
      IO.write(appFile, builder.toString)    
    }
    Seq(appFile) ++ bps.toSeq
  }
}