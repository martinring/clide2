package clide.assistants

import clide.models._
import scala.concurrent._
import clide.collaboration._

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
trait AssistBehavior {
  val noop: Future[Unit] = Future.successful(())
  
  /**
   * Everything that needs to be set up can be set up here. It is guaranteed, that
   * this method will be called first and no other method will be called until the
   * execution has been completed.
   *
   * @param project the project, the assistant is watching
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta.    
   */
  def start(project: ProjectInfo): Future[Unit]

  /**
   * This method will be called, before the assistant will be disposed. Any resources
   * that need to be released can be released here.
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta.    
   */
  def stop: Future[Unit]

  /**
   * Should return a set of mime types that the assistant will automatically
   * react on. If the set is empty, the assistant will only be activated if a user
   * actively requests it's help in a specific file or the assistant actively opens
   * a file through it's control.
   */
  def mimeTypes: Set[String]

  /**
   * called when a previously unknown file is added to the assistants scope.
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def fileOpened(file: OpenedFile): Future[Unit]

  /**
   * called when a previously inactive file turns active. (i.e. sombody looks at it)
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def fileActivated(file: OpenedFile): Future[Unit]

  /**
   * called when a previously active file turns inactive (i.e. everybody stopped
   * looking at the file)
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def fileInactivated(file: OpenedFile): Future[Unit]

  /**
   * called when a previously open file is removed from the assistants scope.
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def fileClosed(file: OpenedFile): Future[Unit]

  /**
   * called when a file in the assistants scope was edited.
   * May do long blocking comuptations. Internally it will be executed concurrently
   * while all new updates to the file will be cumulated and will appear as one update
   * after the method returned. Other Events are postponed during execution.
   *
   * @param file the state of the file **after** the edit occured.
   * @param delta the operation that has been performed
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]): Future[Unit]

  /**
   * called when a collaborator joined the session.
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def collaboratorJoined(who: SessionInfo): Future[Unit]

  /**
   * called when a collaborator left the session
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def collaboratorLeft(who: SessionInfo): Future[Unit]

  /**
   * called when some active collaborator moved the cursor in some file that
   * belongs to the assistants scope.
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def cursorMoved(cursor: Cursor): Future[Unit]
  
  /**
   * at least one client is interested in seeing the specified annotation stream
   */
  def annotationsRequested(file: OpenedFile, name: String): Future[Unit]
  
  /**
   * all clients dropped their interest in seeing the specified annotation stream
   */
  def annotationsDisregarded(file: OpenedFile, name: String): Future[Unit]
  
  /**
   * called when a chat message arrives
   * @param from username of the sender
   * @param msg the message content
   * @param tpe optional message type (TODO: Make enumeration)
   * @param timestamp
   * @return a boolean indicating the point in time when execution can be continued. incoming
   *         messages will be automatically accumulated where possible so that you will receive 
   *         e.g. only one `fileChanged` notification afterwards with a combined delta. 
   */
  def receiveChatMessage(from: SessionInfo, msg: String, tpe: Option[String], timestamp: Long): Future[Unit]
}