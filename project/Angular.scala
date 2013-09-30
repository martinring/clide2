import sbt._
import sbt.Keys._
import play.Project
import play.Keys._
import play.PlayExceptions._
import java.io.File
import java.io.FileReader
import scala.collection.SortedSet

object Angular {   
  val moduleOptions = SettingKey[Seq[String]]("angular-module-options")
  val moduleDirs = SettingKey[Map[String,(String,String,Boolean)]]("angular-module-directories")
  val otherModules = SettingKey[Map[String,String]]("angular-other-modules")
  val configDir = SettingKey[String]("angular-config-directory")       
  
  val defaultSettings = Seq[Setting[_]](
    resourceGenerators in Compile := Seq.empty[sbt.Task[Seq[java.io.File]]],    
    moduleOptions := Seq.empty[String],
    configDir := "config",
    otherModules := Map(),
    moduleDirs := Map()
  )
    
  // (moduleName -> (path,name)*)*  
  private val previous = scala.collection.mutable.Map[String,SortedSet[String]]()

  private object State {
    var changed = false
    var baseDependencies = Set[String]()
    var modules = Map[String,Seq[ModuleDeclaration]]()
  }
  
  private trait HeaderLine
  
  private case class ModuleDeclaration(
      kind: String, 
      module: String,
      name: Option[String]) extends HeaderLine
      
  private case class RequireStatement(
      what: String,
      where: Option[String]) extends HeaderLine
  
  private object ModuleHeaderParser extends scala.util.parsing.combinator.RegexParsers {
    def header: Parser[Option[(ModuleDeclaration,Seq[HeaderLine])]] = opt(decl ~ rep(req) ^^
      { case dec ~ req => (dec,req) })
    
    def decl: Parser[ModuleDeclaration] = 
      (kind ~! opt(module) ~ opt(identifier)) ^^ 
      { case k ~ m ~ i => ModuleDeclaration(k,m.mkString("."),i) }
      
    def req: Parser[HeaderLine] =       
      ("@require".r ~! (identifier ~ opt("from".r ~> path))) ^^ 
      { case _ ~ (what ~ where) => RequireStatement(what,where) }
    
    def identifier: Parser[String] = """([\-a-zA-Z]+)""".r ^^ ( _.toString )
    
    def path: Parser[String] = """([/\-a-zA-Z]+)""".r ^^ ( _.toString )
    
    val kinds = Seq(
        "directive",
        "controller",
        "config",
        "service",
        "filter",
        "factory",
        "run",
        "provider")
        
    def kind: Parser[String] = 
      kinds.map { case k => "@"+k ^^^ k }
           .foldRight { failure("expected module declaration"): Parser[String] }
                      { (x,y) => y | x }
    
    def module: Parser[Seq[String]] = repsep(identifier,".") <~ ":"
    
    override val whiteSpace = """[\s#]+""".r
  }
 
  lazy val ModuleCompiler = play.Project.AssetsCompiler("module",
    (_ ** "*.coffee"),
    coffeescriptEntryPoints,
    { (name, min) => name.replace(".coffee", if (min) ".min.js" else ".js") },
    { (moduleFile, options) =>            
      import scala.util.control.Exception._
      
      val handle = new FileReader(moduleFile)      
      
      val r = ModuleHeaderParser.parse(ModuleHeaderParser.header,handle)
      r match {
        case ModuleHeaderParser.Success(v,_) => handle.close(); v match {
          case Some((ModuleDeclaration(kind,module,name),others)) =>
            println(v.get)
          case None => // nothing            
        }          
        case ModuleHeaderParser.NoSuccess(msg,next) => 
          handle.close()          
          throw AssetCompilationException(Some(moduleFile),msg,Some(next.pos.line),Some(next.pos.column))
      }                  
              
      val jsSource = play.core.coffeescript.CoffeescriptCompiler.compile(moduleFile, options)            
      val minified = catching(classOf[CompilationException]).opt(play.core.jscompile.JavascriptCompiler.minify(jsSource, Some(moduleFile.getName())))
      
      (jsSource, minified, Seq(moduleFile))
    },
    coffeescriptOptions
  )
  
  private def string(any: Any) = "'" + any.toString() + "'"

  val BoilerplateGenerator = (resourceManaged in Compile, sourceDirectory in Compile, cacheDirectory, name, version, moduleDirs, otherModules, configDir) map { (outDir,sourceDir,cache,appName,appVersion,moduleDirs,otherModules,configDir) =>    
    val bps = moduleDirs.map { case (what,(ngf,postfix,capitalize)) =>
      val inFiles = ((sourceDir / "assets" / "javascripts" / what) * "*.coffee").get
      val names = SortedSet(inFiles.map(_.getName.dropRight(7)) :_*)
      val outFile = outDir / "public" / "javascripts" / (what+".js")
      if (previous.get(what).map(_ != names).getOrElse(true)) {        
        previous(what) = names			 
		val builder = new StringBuilder("define([")
		builder ++= names.map(file => "'"+what+"/"+file+"'").mkString(",")
		builder ++= "],function("
		builder ++= names.mkString(",")
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
      val builder = new StringBuilder("define([")
  	  builder ++= (configs.map(file=>string(configDir+"/"+file)).toSeq ++ moduleDirs.keys.map(string).toSeq).mkString(",")      
      builder ++= "],function("
      builder ++= (configs.toSeq).mkString(",")
      builder ++= "){var app=angular.module('"+appName+"',["
      builder ++= (moduleDirs.keys.map(f=>"'"+appName+"."+f+"'") ++ otherModules.values.map(f=>"'"+f+"'")).mkString(",") 
      builder ++= "]);"
      builder ++= configs.map(f=>"app.config("+f+");").mkString
      builder ++= "app.value('version','"+appVersion+"');return app"
      builder ++= "})"
      IO.write(appFile, builder.toString)    
    }
    Seq(appFile) ++ bps.toSeq
  }
}