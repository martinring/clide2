##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU Lesser General Public License as           ##
##   published by the Free Software Foundation, either version 3 of           ##
##   the License, or (at your option) any later version.                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU Lesser General Public         ##
##   License along with Clide.                                                ##
##   If not, see <http://www.gnu.org/licenses/>.                              ##
##                                                                            ##

### @service services:Files ###
define ['routes','util/actorSocket'], (routes,ActorSocket) -> ($q,$http,$timeout,Toasts) ->
  dirs = []
  currentDirId = null
  (username, project, path) ->
    url = routes.clide.web.controllers.Projects.fileBrowser(username,project).webSocketURL()
    new ActorSocket url, "#{username}/#{project}/fileBrowser", (context) ->
      data:
        currentDir: null
      preStart: -> if path?
        context.setReceiveTimeout 100
        context.tell { t: 'explore', path: path }
      interface:
        explore     : (path) ->
          context.tell { t: 'explore', path: path }
        browseTo    : (path) -> context.tell { t: 'browse', path: path }
        delete      : (path) -> context.tell { t: 'rm', path: path }
        touchFile   : (path) -> context.tell { t: 'touchFile', path: path }
        touchFolder : (path) -> context.tell { t: 'touchFolder', path: path }
      receive: (msg) -> switch msg.t
        when 'e'
          Toasts.push 'danger', msg.c
        when 'timeout'
          context.tell { t: 'flush', blowup: [1..1000] }
        when 'newfile'
          f = -> dirs[msg.c.parent]?.files.push msg.c
          if msg.c.parent is currentDirId
            $timeout f, 0
          else f()
        when 'rmfile'
          f = ->
            if dirs[msg.c.parent]?
              for file, j in dirs[msg.c.parent].files
                if file.id is msg.c.id
                  dirs[msg.c.parent].files.splice(j,1)
                  return
          if msg.c.parent is currentDirId
            $timeout f, 0
          else f()
        when 'folder'
          context.setReceiveTimeout(null)
          path = [{name: '$home', path: []}]
          for segment, i in msg.info.path
            p = path[i].path.slice()
            p.push(segment)
            path.push
              name: segment
              path: p
          $timeout((->
            dirs[msg.info.id] =
              info: msg.info
              path: path
              files: msg.files
            currentDirId = msg.info.id
            context.data.currentDir = dirs[currentDirId]),0)
