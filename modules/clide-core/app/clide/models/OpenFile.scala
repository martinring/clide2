package clide.models
  
case class OpenedFile(
    info: FileInfo, 
    state: String, 
    revision: Long)

