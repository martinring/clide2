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

define ->
  time = -> (new Date).toLocaleString()
  actors = { }
  id = 0
  nextId = -> id++
  (url, name, behaviorFactory) ->
    if actors[name]?
      actors[name].stop()
      #throw new Error "an actor with that name already exists"
    inbox  = []
    outbox = []

    context =
      log:
        debug: (msg) -> console.debug "[#{time()}] [#{name}] #{msg}"
        info:  (msg) -> console.info  "[#{time()}] [#{name}] #{msg}"
        warn:  (msg) -> console.warn  "[#{time()}] [#{name}] #{msg}"
        error: (msg) -> console.error "[#{time()}] [#{name}] #{msg}"

    behavior = behaviorFactory(context)

    context.data = behavior.data

    socket = undefined

    addListeners = ->
      socket.onmessage = (e) ->
        resetTimeout()
        msg = JSON.parse(e.data)
        try
          behavior.receive(msg)
          console.debug "[#{time()}] [#{name}] received", msg
        catch error
          console.warn "[#{time()}] [#{name}] message failed", msg
          console.error "[#{time()}] [#{name}]", error

      socket.onerror = (e) ->
        service.state = 'failed'
        console.error "[#{time()}] [#{name}] failed", e

      socket.onclose = () ->
        service.state = 'closed'
        console.debug "[#{time()}] [#{name}] closed"
        behavior.receive
          t: 'terminated'
        behavior.postStop?()

      socket.onopen = () ->
        service.state = 'open'
        console.debug "[#{time()}] [#{name}] opened"
        behavior.preStart?()
        while outbox.length > 0
          msg = outbox.pop()
          send(msg)

    service =
      data:      behavior.data
      interface: behavior.interface
      state:     'init'
      stop:      -> socket.close()
      restart:   ->
        socket?.close()
        socket = new WebSocket(url)
        service.state = 'connecting'
        addListeners()

    ready = -> socket?.readyState is WebSocket.OPEN

    receiveTimeoutSpan = undefined
    receiveTimeout     = undefined

    onTimeout = () ->
      behavior.receive
        t: 'timeout'

    resetTimeout = () ->
      clearTimeout(receiveTimeout)
      if receiveTimeoutSpan?
        receiveTimeout = setTimeout(onTimeout,receiveTimeoutSpan)

    context.setReceiveTimeout = (ms) ->
      if ms? and ms > 10
        receiveTimeoutSpan = ms
      else
        receiveTimeoutSpan = undefined
        resetTimeout()

    send = (msg) ->
      socket.send(JSON.stringify(msg))
      console.debug "[#{time()}] [#{name}] sent", msg
      resetTimeout()

    context.restart = () ->
      socket?.close()
      socket = new WebSocket(url)

    context.tell = (msg, timeout = 0, retries = 0) ->
      if timeout > 0
        msg.$ID = nextId()
      if ready()
        send(msg)
      else
        outbox.push(msg)

    context.tellSecure = (msg) -> context.tell(msg,500,20)

    actors[name] = service
    service.restart()

    return service
