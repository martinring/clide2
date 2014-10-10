/*
 * Most of this is copyright 2010 Twitter, Inc.
 *
 * Licensed under the Apache License, Version 2.0 
 * 
 *     http://www.apache.org/licenses/LICENSE-2.0
 */

package clide.scala

import scala.reflect.io.VirtualDirectory
import scala.tools.nsc.reporters.AbstractReporter
import java.io.File
import java.net.URLClassLoader
import java.util.jar.JarFile
import scala.collection.mutable.ListBuffer
import scala.reflect.internal.util.{BatchSourceFile, Position}
import scala.tools.nsc.interactive.Global
import scala.tools.nsc.interpreter.AbstractFileClassLoader
import scala.collection.mutable.SortedSet
import scala.tools.nsc.interactive.Response
import scala.io.Source
import scala.collection.mutable.Buffer
import scala.tools.refactoring.common.PimpedTrees
import scala.tools.refactoring.common.CompilerAccess
import clide.models.OpenedFile
import scala.reflect.internal.util.OffsetPosition
import scala.util.control.NonFatal

trait ScalaCompiler extends CompilerAccess with PimpedTrees { self: ScalaBehavior =>    
  /*
   * For a given FQ classname, trick the resource finder into telling us the containing jar.
   */
  private def classPathOfClass(className: String) = try {
    val resource = className.split('.').mkString("/", "/", ".class")
    val path = getClass.getResource(resource).getPath
    if (path.indexOf("file:") >= 0) {
      val indexOfFile = path.indexOf("file:") + 5
      val indexOfSeparator = path.lastIndexOf('!')
      List(path.substring(indexOfFile, indexOfSeparator))
    } else {
      require(path.endsWith(resource))
      List(path.substring(0, path.length - resource.length + 1))
    }
  }
  
  private lazy val compilerPath = try {
    classPathOfClass("scala.tools.nsc.Interpreter")    
  } catch {
    case e: Throwable =>
      throw new RuntimeException("Unable to load Scala interpreter from classpath (scala-compiler jar is missing?)", e)
  }
  
  private lazy val libPath = try {    
    classPathOfClass("scala.AnyVal")
  } catch {
    case e: Throwable =>
      throw new RuntimeException("Unable to load scala base object from classpath (scala-library jar is missing?)", e)
  }
  
 /*
   * Try to guess our app's classpath.
   * This is probably fragile.
   */
  lazy val impliedClassPath: List[String] = {
    def getClassPath(cl: ClassLoader, acc: List[List[String]] = List.empty): List[List[String]] = {
      val cp = cl match {
        case urlClassLoader: URLClassLoader => urlClassLoader.getURLs.filter(_.getProtocol == "file").
          map(u => new File(u.toURI).getPath).toList
        case _ => Nil
      }
      cl.getParent match {
        case null => (cp :: acc).reverse
        case parent => getClassPath(parent, cp :: acc)
      }
    }

    val classPath = getClassPath(this.getClass.getClassLoader)
    val currentClassPath = classPath.head

    // if there's just one thing in the classpath, and it's a jar, assume an executable jar.
    currentClassPath ::: (if (currentClassPath.size == 1 && currentClassPath(0).endsWith(".jar")) {
      val jarFile = currentClassPath(0)
      val relativeRoot = new File(jarFile).getParentFile()
      val nestedClassPath = new JarFile(jarFile).getManifest.getMainAttributes.getValue("Class-Path")
      if (nestedClassPath eq null) {
        Nil
      } else {
        nestedClassPath.split(" ").map { f => new File(relativeRoot, f).getAbsolutePath }.toList
      }
    } else {
      Nil
    }) ::: classPath.tail.flatten
  }
  
  
  val target = new VirtualDirectory("<memory>", None)
  
  lazy val settings = new scala.tools.nsc.Settings  
  settings.outputDirs.setSingleOutput(target)  
  
  val pathList = compilerPath ::: libPath
  settings.bootclasspath.value = pathList.mkString(File.pathSeparator)
  settings.classpath.value = (pathList ::: impliedClassPath).mkString(File.pathSeparator)
  //settings.YpresentationDebug.value = true
  //settings.YpresentationVerbose.value = true
  
  val messages = collection.mutable.Map.empty[String,SortedSet[(Int,Int,String,String)]]  
  val identifiers = collection.mutable.Map.empty[String,SortedSet[(Int,Int,Option[String],Seq[String])]]
  val substitutions = collection.mutable.Map.empty[String,SortedSet[(Int,Int,String)]]
  val implicits = collection.mutable.Map.empty[String,SortedSet[(Int,Int,String)]]
  
  def markImplicit(pos: Position, t: String) = if (pos.isDefined) {    
    if (!implicits.isDefinedAt(pos.source.file.name))
      implicits(pos.source.file.name) = SortedSet.empty
    val (start,length) =
      (pos.startOrPoint, pos.endOrPoint - pos.startOrPoint)
    implicits(pos.source.file.name) += ((start,length,t))
  }
  
  def substitute(pos: Position, symbol: String) = if (pos.isDefined) {
    if (!substitutions.isDefinedAt(pos.source.file.name))
      substitutions(pos.source.file.name) = SortedSet.empty
    val (start,length) =
      (pos.startOrPoint, pos.endOrPoint - pos.startOrPoint)
    substitutions(pos.source.file.name) += ((start,length,symbol))    
  }
  
  def identifier(pos: Position, kind: String*): Unit = identifier(pos, None, kind :_*)
  
  def identifier(pos: Position, t: Option[String], kind: String*): Unit = if (pos.isDefined) {    
    if (!identifiers.isDefinedAt(pos.source.file.name))
      identifiers(pos.source.file.name) = SortedSet.empty(Ordering.by(x => (x._1,x._2)))
    val (start,length) =
      (pos.startOrPoint, pos.endOrPoint - pos.startOrPoint)  
    identifiers(pos.source.file.name) += ((start,length,t,kind))
  }
  
  lazy val reporter = new AbstractReporter {
    val settings = ScalaCompiler.this.settings    
    
    def display(pos: Position, message: String, severity: Severity) = if (pos.isDefined) {
      val severityName = severity match {
        case ERROR => "error"
        case WARNING => "warning"        
        case INFO => "info"
        case _ => "warning"
      }
      val (start,length) = try {
        (pos.startOrPoint, pos.endOrPoint - pos.startOrPoint)
      } catch {
        case NonFatal(_) => (0,0)        
      }
      if (!messages.isDefinedAt(pos.source.file.name)) messages(pos.source.file.name) = SortedSet.empty
      messages(pos.source.file.name) += ((start, length, severityName, message))
      annotate()
    }
    
    def displayPrompt {
      // no
    }
    
    override def reset {
      super.reset
    }
  }

  lazy val global = new Global(settings, reporter)
  
  def compilationUnitOfFile(f: tools.nsc.io.AbstractFile): Option[global.CompilationUnit] = None
  
  var classLoader = new AbstractFileClassLoader(target, this.getClass.getClassLoader)
  
  def reset() = try {
    reporter.reset()
    classLoader = new AbstractFileClassLoader(target, this.getClass.getClassLoader)
  }
      
  def complete(state: OpenedFile, p: Int)(respond: List[global.Member] => Unit) = try {    
    val reloaded = new Response[Unit]
    val source = new BatchSourceFile(state.info.path.mkString("/"), state.state)
    global.askReload(List(source), reloaded)
    
    val c = reloaded.get.left.foreach { _ =>      
      val tcompletion = new Response[List[global.Member]]      
	    val pos = global.ask(() => new OffsetPosition(source, p))
	    global.askTypeCompletion(pos, tcompletion)
	    tcompletion.get(5000).get match {
        case Left(members) => global.ask( () => respond(members) )
        case Right(e) =>
          println("error " + e.getMessage())
          val scompletion = new Response[List[global.Member]]
          global.askScopeCompletion(pos, scompletion)         
	        scompletion.get(5000).get.left.foreach { members =>
	          global.ask( () => respond(members) )        
	        }
      }
    }
  }
  
  def annotationsFromTree(tree: global.Tree): Unit = if (tree.pos.isDefined && tree.pos.isRange) tree match {    
    case t: global.TypeTree =>
      val classes = "ref" :: "type" ::
        (if (t.symbol.isTypeParameter) List("param") else Nil)
      identifier(t.namePosition, classes :_*)
      t.children.foreach(annotationsFromTree(_))      
    case c: global.TypeDef =>
      val classes = "def" :: "type" :: 
        (if (c.symbol.isTypeParameter) List("param") else Nil)        
      identifier(c.namePosition,classes :_*)
      c.children.foreach(annotationsFromTree(_))
    case c: global.ClassDef =>
      identifier(c.namePosition, "def", "type")
      c.children.foreach(annotationsFromTree(_))
    case c: global.ModuleDef =>
      identifier(c.namePosition, "def", "module")
      c.children.foreach(annotationsFromTree(_))    
    case c: global.Bind =>      
      identifier(c.namePosition, "def", "local")      
      c.children.foreach(annotationsFromTree(_))    
    case c: global.ValDef =>
      val classes = "def" :: "val-def" ::
        (if (c.symbol.isLocal) List("local") else Nil) ++
        (if (c.symbol.isParameter) List("param") else Nil) ++
        (if (c.symbol.isVar) List("var-def") else Nil)
      global.ask(() => identifier(c.namePosition,Some(c.symbol.signatureString), classes :_*))
      c.children.foreach(annotationsFromTree(_))          
    case c: global.DefDef =>
      val classes = "def" :: "def-def" ::
        (if (c.symbol.isLocal) List("local") else Nil) ++
        (if (c.symbol.isParameter) List("param") else Nil) ++
        (if (c.symbol.isVar) List("var-def") else Nil)
      global.ask(() => identifier(c.namePosition,Some(c.symbol.signatureString), classes :_*))
      c.children.foreach(annotationsFromTree(_))
    case a: global.Apply if a.symbol != global.NoSymbol =>      
      if (a.symbol.isImplicit) {
        markImplicit(a.namePosition, a.args.apply(0).tpe.toLongString + " -> " + a.tpe.toLongString)        
      }
      a.children.foreach(annotationsFromTree(_))
    case c: global.Select if c.symbol != global.NoSymbol =>
      val classes = "ref" :: "select" ::      
        global.ask(() => (if (c.symbol.isDeprecated) List("deprecated") else Nil)) ++        
        (if (c.symbol.isVar) List("variable") else Nil) ++
        (if (c.symbol.isLocal) List("local") else Nil) ++
        (if (c.symbol.isValueParameter) List("param") else Nil) ++
        (if (c.symbol.isModule) List("module") else Nil) ++
        (if (c.symbol.isConstructor) List("constructor", "type") else Nil)
      global.ask(() => identifier(c.namePosition,Some(c.symbol.signatureString), classes :_*))
      val substs = List(
          "<=" -> "≤", 
          ">=" -> "≥",
          "&&" -> "",
          "!=" -> "≠",
          "==" -> "≡",
          "&&" -> "∧",
          "||" -> "∨")
      substs.find(_._1 == c.name.decoded).map(x => substitute(c.namePosition, x._2))
      c.children.foreach(annotationsFromTree(_))
    case i: global.Ident if i.symbol != global.NoSymbol =>      
      val classes = "ref" :: "ident" ::
        global.ask(() => (if (i.symbol.isDeprecated) List("deprecated") else Nil)) ++
        (if (i.symbol.isVar) List("variable") else Nil) ++
        (if (i.symbol.isLocal) List("local") else Nil) ++
        (if (i.symbol.isValueParameter) List("param") else Nil) ++
        (if (i.symbol.isModule) List("module") else Nil) ++
        (if (i.symbol.isType) List("type") else Nil)
      global.ask(() => identifier(i.namePosition,Some(i.symbol.signatureString),classes :_*))      
      i.children.foreach(annotationsFromTree(_))
    case t: global.Tree =>
      t.children.foreach(annotationsFromTree(_))
  }   
  
  def compile(state: OpenedFile) = try {    
    messages.values.foreach(_.clear)   
    val source = new BatchSourceFile(state.info.path.mkString("/"), state.state)
    val reloaded = new Response[Unit]
    global.askReload(List(source), reloaded)
    reloaded.get.left.foreach { _ =>
      val tree = new Response[global.Tree]
      global.askLoadedTyped(source, tree)
      tree.get.left.foreach { tree =>
        identifiers.get(source.path).foreach(_.clear())
        implicits.get(source.path).foreach(_.clear())
        substitutions.get(source.path).foreach(_.clear())
        annotationsFromTree(tree)
        annotateSemantics()
        annotate()
      }
    }
  }
}