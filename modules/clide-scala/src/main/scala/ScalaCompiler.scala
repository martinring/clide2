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
import clide.models.OpenedFile
import scala.reflect.internal.util.OffsetPosition

trait ScalaCompiler { self: ScalaBehavior =>
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
    classPathOfClass("scala.ScalaObject")
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
  settings.warnEverything.value = true
  
  val pathList = compilerPath ::: libPath
  settings.bootclasspath.value = pathList.mkString(File.pathSeparator)
  settings.classpath.value = (pathList ::: impliedClassPath).mkString(File.pathSeparator)
  settings.YpresentationDebug.value = true
  settings.YpresentationVerbose.value = true
  
  val messages = collection.mutable.Map.empty[String,SortedSet[(Int,Int,String,String)]]
  
  lazy val reporter = new AbstractReporter {
    val settings = ScalaCompiler.this.settings    
    
    def display(pos: Position, message: String, severity: Severity) {      
      severity.count += 1
      val severityName = severity match {
        case ERROR => "error"
        case WARNING => "warning"
        case _ => "info"
      }
      val (start,length) = try {
        (pos.startOrPoint, pos.endOrPoint - pos.startOrPoint)
      } catch {
        case _: Throwable => (0,0)        
      }
      messages(pos.source.file.name) += ((start, length, severityName, message))
    }
    
    def displayPrompt {
      // no
    }
    
    override def reset {
      super.reset
      messages.values.foreach(_.clear)
    }
  }

  lazy val global = new Global(settings, reporter)
  
  var classLoader = new AbstractFileClassLoader(target, this.getClass.getClassLoader)
  
  def reset() = try {
    reporter.reset()
    classLoader = new AbstractFileClassLoader(target, this.getClass.getClassLoader)
  }
      
  def complete(state: OpenedFile, p: Int)(respond: List[global.Member] => Unit) = try {
    println("completing")
    val reloaded = new Response[Unit]
    val source = new BatchSourceFile(state.info.path.mkString("/"), state.state)
    global.askReload(List(source), reloaded)
    
    val c = reloaded.get.left.foreach { _ =>      
      val completion = new Response[List[global.Member]]
	    val pos = global.ask(() => new OffsetPosition(source, p))
	    global.askTypeCompletion(pos, completion)
	    completion.get(5000).get.left.foreach { members =>
        global.ask( () => respond(members) )        
      }
    }
  }
  
  def compile(state: OpenedFile,done: => Unit) = try {
    println("compiling")
    val reloaded = new Response[Unit]
    val source = new BatchSourceFile(state.info.path.mkString("/"), state.state)
    global.askReload(List(source), reloaded)    
    reloaded.get.left.foreach { _ =>
      println(messages)
      done 
    }
  }
  
}