 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.assistants

import clide.collaboration.Annotations
import clide.models.OpenedFile
import clide.collaboration.Operation
import clide.models.ProjectInfo
import clide.models.SessionInfo
import akka.actor.IO.Iteratee
import scala.concurrent.Future

/**
 * @typeParam State
 * 
 * @author Martin Ring <martin.ring@dfki.de>
 */
trait AssistantBehavior { self: AssistantControl =>
  /**
   * Everything that needs to be set up can be set up here. It is guaranteed, that
   * this method will be called first and no other method will be called until this
   * method has been completely executed.
   * 
   * @param project the project, the assistant is watching
   */
  def initialize(project: ProjectInfo): Unit
  
  /**
   * This method will be called, before the assistant will be disposed. Any resources
   * that need to be released can be released here.
   */
  def finalize: Unit
  
  /**
   * Should return a set of mime types that the assistant will automatically
   * react on. If the set is empty, the assistant will only be activated if a user
   * actively requests it's help in a specific file.  
   */
  def mimeTypes: Seq[String]
  
  /**
   * called when a previously unknown file is added to the assistants scope.
   */
  def fileOpened(file: OpenedFile): Unit
  
  /**
   * called when a previously inactive file turns active. (i.e. sombody looks at it)
   */
  def fileActivated(file: OpenedFile): Unit
  
  /**
   * called when a previously active file turns inactive (i.e. everybody stopped 
   * looking at the file)
   */
  def fileInactivated(file: OpenedFile): Unit
  
  /**
   * called when a previously open file is removed from the assistants scope.
   */
  def fileClosed(file: OpenedFile): Unit
  
  /**
   * called when a file in the assistants scope has been edited.
   * @param file the state of the file **after** the edit occured.
   * @param delta the operation that has been performed
   */
  def fileChanged(file: OpenedFile, delta: Operation): Unit
  
  /**
   * called when a collaborator joined the session.
   */
  def collaboratorJoined(who: SessionInfo): Unit
  
  /**
   * called when a collaborator left the session
   */
  def collaboratorLeft(who: SessionInfo): Unit
  
  /**
   * called when some active collaborator moved the cursor in some file that
   * belongs to the assistants scope.
   * 
   * @owner the collaborator that is the owner of the cursor
   * @offset the new position of the cursor (as an absolute offset)
   */
  def cursorMoved(file: OpenedFile, owner: SessionInfo, offset: Int): Unit
}