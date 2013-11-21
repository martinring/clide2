/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */
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
