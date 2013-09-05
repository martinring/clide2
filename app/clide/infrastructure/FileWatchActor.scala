package clide.infrastructure

import akka.actor.Actor
import java.io.File
import java.nio.file.FileSystems

class FileWatchActor extends Actor {
  val watchService = FileSystems.getDefault().newWatchService();
  
  def receive = {
    case _ => 
  }
}

object FileWatchActor {
  
}