##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU General Public License as published by     ##
##   the Free Software Foundation, either version 3 of the License, or        ##
##   (at your option) any later version.                                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU General Public License        ##
##   along with Clide.  If not, see <http://www.gnu.org/licenses/>.           ##
##                                                                            ##

## Loosely Based on the javascript ot implementation 'ot.js' by Tim Baumann (MIT
## License) see https://github.com/Operational-Transformation/ot.js

define ->
  class Client
    constructor: (revision) ->
      @revision          = revision # the next expected revision number
      @state             = new Synchronized # start state
      @annotation        = null
      @annotationTimeout = null

    setAnnotationTimeout: () ->
      instance = this
      f = ->
        instance.annotationTimeout = null
        instance.annotate(instance.annotation) if instance.annotation?
      @annotationTimeout = window.setTimeout f, 250 # Maximum of 4 Annotations per second

    setState: (state) ->
      @state = state

    applyClient: (operation) ->
      @annotation = @annotation?.transform(operation)
      @setState @state.applyClient(this, operation)

    annotate: (annotation) ->
      @state.annotate(this, annotation)

    applyServer: (operation) ->
      @annotation = @annotation?.transform(operation)
      @revision++
      @setState @state.applyServer(this, operation)

    serverAckEdit: ->
      @revision++
      @setState @state.serverAck(this)

    serverReconnect: ->
      @state.resend? this

    syncState: ->
      @state.syncState

    transformAnnotation: (annotation) ->
      @state.transformAnnotation annotation

    sendAnnotation: (revision, annotation, name) ->
      throw new Error("sendAnnotation must be defined in child class")

    sendOperation: (revision, operation) ->
      throw new Error("sendOperation must be defined in child class")

    applyOperation: (operation) ->
      throw new Error("applyOperation must be defined in child class")

    class Synchronized
      applyClient: (client, operation) ->
        client.sendOperation client.revision, operation
        new Pending(operation)

      applyServer: (client, operation) ->
        client.applyOperation operation
        this

      serverAck: (client) ->
        throw new Error("There is no pending operation.")

      syncState: 0

      annotate: (client, annotation) ->
        client.annotation = null
        if client.annotationTimeout?
          client.annotation = annotation
        else
          client.sendAnnotation client.revision, annotation, 'selection'
          client.setAnnotationTimeout()

      transformAnnotation: (annotation) ->
        annotation

    class Pending
      constructor: (outstanding) ->
        @outstanding = outstanding

      applyClient: (client, operation) ->
        new Buffering(@outstanding, operation)

      applyServer: (client, operation) ->
        pair = operation.constructor.transform(@outstanding, operation)
        client.applyOperation pair[1]
        new Pending(pair[0])

      syncState: 1

      serverAck: (client) ->
        if not client.annotationTimeout? and client.annotation?
          client.sendAnnotation client.revision, client.annotation, 'selection'
          client.annotation = null
          client.setAnnotationTimeout()
        new Synchronized

      annotate: (client, annotation) ->
        client.annotation = annotation

      transformAnnotation: (annotation) ->
        annotation.transform @outstanding

      resend: (client) ->
        client.sendOperation client.revision, @outstanding

    class Buffering
      constructor: (outstanding, buffer) ->
        @outstanding = outstanding
        @buffer = buffer

      applyClient: (client, operation) ->
        # Compose the user's changes onto the buffer
        newBuffer = @buffer.compose(operation)
        new Buffering(@outstanding, newBuffer)

      applyServer: (client, operation) ->
        transform = operation.constructor.transform
        pair1 = transform(@outstanding, operation)
        pair2 = transform(@buffer, pair1[1])
        client.applyOperation pair2[1]
        new Buffering(pair1[0], pair2[0])

      syncState: 2

      serverAck: (client) ->
        client.sendOperation client.revision, @buffer
        if not client.annotationTimeout? and client.annotation?
          client.sendAnnotation client.revision, client.annotation, 'selection'
          client.annotation = null
          client.setAnnotationTimeout()
        new Pending(@buffer)

      annotate: (client, annotation) ->
        client.annotation = annotation

      transformAnnotation: (annotation) ->
        annotation.transform(@outstanding).transform @buffer

      resend: (client) ->
        client.sendOperation client.revision, @outstanding
