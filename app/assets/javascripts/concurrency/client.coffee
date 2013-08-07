define ->   
  class Client       
    constructor: (revision) ->
      @revision = revision # the next expected revision number
      @state = new Synchronized # start state      

    setState: (state) ->
      @state = state

    applyClient: (operation) ->
      @setState @state.applyClient(this, operation)

    applyServer: (revision, operation) ->
      if revision isnt ++@revision
        throw new Error("inconsistent revisions... something is broken!")
      @setState @state.applyServer(this, operation)

    serverAck: ->
      @revision++
      @setState @state.serverAck(this)

    serverReconnect: ->
      @state.resend this  if typeof @state.resend is "function"

    transformCursor: (cursor) ->
      @state.transformCursor cursor

    sendOperation: (revision, operation) ->
      throw new Error("sendOperation must be defined in child class")

    applyOperation: (operation) ->
      throw new Error("applyOperation must be defined in child class")

    class Synchronized      
      applyClient: (client, operation) ->
        client.sendOperation client.revision, operation
        new AwaitingConfirm(operation)

      applyServer: (client, operation) ->
        client.applyOperation operation
        this

      serverAck: (client) ->
        throw new Error("There is no pending operation.")

      transformCursor: (cursor) ->
        cursor
    
    class AwaitingConfirm
      constructor: (outstanding) ->
        @outstanding = outstanding

      applyClient: (client, operation) ->
        new AwaitingWithBuffer(@outstanding, operation)

      applyServer: (client, operation) ->
        pair = operation.constructor.transform(@outstanding, operation)
        client.applyOperation pair[1]
        new AwaitingConfirm(pair[0])

      serverAck: (client) ->
        new Synchronized

      transformCursor: (cursor) ->
        cursor.transform @outstanding

      resend: (client) ->
        client.sendOperation client.revision, @outstanding

    class AwaitingWithBuffer 
      constructor: (outstanding, buffer) ->
        @outstanding = outstanding
        @buffer = buffer  

      applyClient: (client, operation) ->        
        # Compose the user's changes onto the buffer
        newBuffer = @buffer.compose(operation)
        new AwaitingWithBuffer(@outstanding, newBuffer)

      applyServer: (client, operation) ->
        transform = operation.constructor.transform
        pair1 = transform(@outstanding, operation)
        pair2 = transform(@buffer, pair1[1])
        client.applyOperation pair2[1]
        new AwaitingWithBuffer(pair1[0], pair2[0])

      serverAck: (client) ->
        client.sendOperation client.revision, @buffer
        new AwaitingConfirm(@buffer)

      transformCursor: (cursor) ->
        cursor.transform(@outstanding).transform @buffer

      resend: (client) ->
        client.sendOperation client.revision, @outstanding