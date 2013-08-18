import sbt._
import play.Project
import Keys._
import PlayKeys._
import PlayExceptions._
import java.io.File
import scala.collection.SortedSet

trait Angular {   
  val ngModuleOptions = SettingKey[Seq[String]]("angular-module-options")
  val ngModuleDirs = SettingKey[Map[String,(String,String,Boolean)]]("angular-module-directories")
  val ngOtherModules = SettingKey[Map[String,String]]("angular-other-modules")
  val ngConfigDir = SettingKey[String]("angular-config-directory")   
    
  private val previous = scala.collection.mutable.Map[String,SortedSet[String]]()    
  
  val ngDefaultSettings = Seq[Setting[_]](
    resourceGenerators in Compile := Seq.empty[sbt.Task[Seq[java.io.File]]],    
    ngModuleOptions := Seq.empty[String],
    ngConfigDir := "config",
    ngOtherModules := Map(),
    ngModuleDirs := Map()
  )
  
  val ngBoilerplateGenerator = (resourceManaged in Compile, sourceDirectory in Compile, cacheDirectory, name, ngModuleDirs, ngOtherModules, ngConfigDir) map { (outDir,sourceDir,cache,appName,moduleDirs,otherModules,configDir) =>                    
    val bps = moduleDirs.map { case (what,(ngf,postfix,capitalize)) =>
      val inFiles = ((sourceDir / "assets" / "javascripts" / what) * "*.coffee").get
      val names = SortedSet(inFiles.map(_.getName.dropRight(7)) :_*)
      val outFile = outDir / "public" / "javascripts" / (what+".js")
      if (previous.get(what).map(_ != names).getOrElse(true)) {        
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
      previous(configDir) = configs
      val builder = new StringBuilder("define(['angular'")
  	  builder ++= configs.map(file => ",'"+configDir+"/"+file+"'").mkString    
      builder ++= otherModules.keys.map(file => ",'"+file+"'").mkString
      builder ++= moduleDirs.keys.map(file => ",'"+file+"'").mkString 
      builder ++= "],function(angular,"
      builder ++= configs.mkString(",")
      builder ++= "){var app=angular.module('"+appName+"',["
      builder ++= (moduleDirs.keys.map(f=>"'clide."+f+"'") ++ otherModules.values.map(f=>"'"+f+"'")).mkString(",") 
      builder ++= "]);"
      builder ++= configs.map(f=>"app.config("+f+");").mkString
      builder ++= "})"
      IO.write(appFile, builder.toString)    
    }
    Seq(appFile) ++ bps.toSeq
  }
 
  lazy val ngModuleCompiler = play.Project.AssetsCompiler("module",
    (_ ** "*.coffee"),
    coffeescriptEntryPoints,
    { (name, min) => name.replace(".coffee", if (min) ".min.js" else ".js") },
    { (moduleFile, options) =>            
      import scala.util.control.Exception._
      val handle = scala.io.Source.fromFile(moduleFile)
      val src = handle.getLines      
      val tempFile = java.io.File.createTempFile(moduleFile.getName(),"module")      
      val writer = new java.io.FileWriter(tempFile)
      
      var imports = Map[String,String]()
      var injects = Map[String,String]()
      
      var header = false
      var code = false
      var line = ""
      
      while (!code && src.hasNext) {
        line = src.next().trim
        if (line.startsWith("#>")) {          
          val words = line.drop(2).trim.split(" *, *| +").iterator
          if (words.hasNext) words.next() match {
            case "module" =>
              header = true
            case "import" => while (words.hasNext) {                
              val path = words.next()
              val name = path.split("\\\\.").last
              imports += path -> name
            }
            case "inject" => while (words.hasNext) {
              val path = words.next
              injects += path -> path
            }                       
          }
        } else if (!line.isEmpty) {
          if (header) {
	        if (imports.isEmpty) {
	          writer.write("define ->")
	        }
	        else {
	          val paths = imports.map{p => "'"+p._1.replace(".","/")+"'"}
	          writer.write("define ["+paths.mkString(",")+"], ("+imports.map(_._2).mkString(",")+") ->")            
	        }
	        if (!injects.isEmpty) {
	          val names = injects.map(p => "'"+p._1+"'")            
	          writer.write("["+names.mkString(",")+",("+injects.map(_._2).mkString(",")+") ->")
	        }
	        writer.write("\n")
          }
          code = true
        }        
      }
      writer.write((if (header) "  " + line else line)+"\n")
      while (src.hasNext) {
        writer.write((if (header) "  " + src.next else src.next)+"\n")
      }
      handle.close()
      if (header && !injects.isEmpty)
        writer.write("]")
      writer.close()
      val jsSource = play.core.coffeescript.CoffeescriptCompiler.compile(tempFile, options)      
      tempFile.delete()
      val minified = catching(classOf[CompilationException]).opt(play.core.jscompile.JavascriptCompiler.minify(jsSource, Some(moduleFile.getName())))
      
      (jsSource, minified, Seq(moduleFile))
    },
    coffeescriptOptions
  )
}