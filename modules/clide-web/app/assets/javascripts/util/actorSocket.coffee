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
  class ActorSocket
    constructor: (@url,@name, @behavior) ->
      @socket = socket = new WebSocket(@url)

      ready = -> socket.readyState = WebSocket.OPEN

      inbox  = []
      outbox = []

      receiveTimeoutSpan = undefined
      receiveTimeout     = undefined

      context = { }

      behavior = @behavior(context)

      onTimeout = () ->
        behavior.receive
          t: 'timeout'

      resetTimeout = () ->
        clearTimeout(receiveTimeout)
        if receiveTimeoutSpan?
          setTimeout(onTimeout,receiveTimeoutSpan)

      context.setReceiveTimeout = (ms) ->
        receiveTimeoutSpan = ms

      send = (msg) ->
        console.debug "[#{name}] sending: ", msg
        socket.send(JSON.stringify(msg))
        resetTimeout()

      socket.onmessage = (e) ->
        resetTimeout()
        msg = JSON.parse(e.data)
        console.debug "[#{name}] received:", msg
        behavior.receive(msg)

      socket.onerror = (e) ->
        console.error error

      socket.onclose = () ->
        log.debug "[#{name}] closed"
        behavior.receive
          t: 'terminated'
        behavior.postStop?()

      socket.onopen = () ->
        behavior.preStart?()
        for msg in outbox
          socket.send(msg)

      context.tell = (msg) ->
        if ready() then send(msg) else outbox.push(msg)
