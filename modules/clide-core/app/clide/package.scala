 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

/** 
 * This is the documentation for clide.
 * 
 * == Package structure ==
 * 
 * The [[clide `clide`]] package contains the Core object which is responsible for
 * setting up the akka microkernel and starting the infrastructure.
 * 
 *  - [[clide.models `clide.models`]] contains the data structures used to represent the
 *    persistent state of the application.
 *  - [[clide.persistence `clide.persistence`]] is the package where the actual data access layer is
 *    defined and set up.
 *  - [[clide.collaboration `clide.collaboration`]] contains the data structures and algorithms which
 *    allow for concurrent editing of text as well as simultaneous synchronized
 *    annotations.
 *  - in [[clide.actors `clide.actors`]] you will find all the actors, that define the 
 *    behaviour of the application. Most important here is the [[clide.actors.UserServer `UserServer`]],
 *    which is the single communication interface for plugins or users.
 *  - [[clide.assistants `clide.assitants`]] contains convenience classes that can be used to
 *    implement non-human collaborative plug-ins, that can assist users in what they are doing. 
 *  - [[clide.util `clide.util`]] contains arbitrary helpers.
 * 
 * @author Martin Ring <martin.ring@dfki.de>
 */
package object clide