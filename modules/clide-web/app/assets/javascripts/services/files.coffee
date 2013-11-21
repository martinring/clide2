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
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects

  socket  = undefined
  dirs = []
  queue = []

  currentDirId = null

  files =
    currentDir: null
    state: 'closed'

  get = (username, project, init) ->
    ws = new WebSocket(pc.fileBrowser(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    socket= ws
    $timeout((-> files.state = 'connecting'),0)
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      switch msg.t
        when 'e'
          Toasts.push 'danger', msg.c
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
            files.currentDir = dirs[currentDirId]),0)
    ws.onopen = (e) ->
      $timeout((-> files.state = 'connected'),0)
      for msg in queue
        ws.send(msg)
      queue = []
    ws.onclose = ws.onerror = (e) ->
      listeners = undefined
      socket = undefined
      $timeout((-> files.state= 'disconnected'),0)

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))
    when WebSocket.OPEN
      data = JSON.stringify(message)
      socket.send(data)

  return (
    info: files
    init: (username, project, init) ->
      socket or get(username, project, init)
    explore: (path) -> send
      t: 'explore'
      path: path
    browseTo: (path,id) -> send
      t: 'browse'
      path: path
    touchFile: (path) -> send
      t: 'touchFile'
      path: path
    touchFolder: (path) -> send
      t: 'touchFolder'
      path: path
    open: (path) -> send
      t: 'open'
      path: path
    select: (path) -> send
      t: 'select'
      path: path
    delete: (path) -> send
      t: 'rm'
      path: path
    create: (path) -> send
      t: 'new'
      path: path or dirs[currentDirId].info.path or []
    close: ->
      socket?.close()
  )
