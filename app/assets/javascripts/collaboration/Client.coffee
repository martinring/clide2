define ->   
  class Client       
    constructor: (revision) ->
      @revision = revision # the next expected revision number
      @state = new Synchronized # start state      

    setState: (state) ->
      @state = state

    applyClient: (operation) ->
      @setState @state.applyClient(this, operation)

    applyServer: (operation) ->
      @revision++
      @setState @state.applyServer(this, operation)

    serverAck: ->
      @revision++
      @setState @state.serverAck(this)

    serverReconnect: ->
      @state.resend? this

    transformAnnotation: (annotation) ->
      @state.transformAnnotation annotation

    sendOperation: (revision, operation, annotation) ->
      throw new Error("sendOperation must be defined in child class")

    applyOperation: (operation) ->
      throw new Error("applyOperation must be defined in child class")

    applyAnnotation: (annotation) ->
      throw new Error("applyOperation must be defined in child class")

    class Synchronized      
      applyClient: (client, operation) ->
        client.sendOperation client.revision, operation
        new AwaitingConfirm(operation,annotation)

      applyServer: (client, operation, annotation) ->
        client.applyOperation operation, annotation
        this

      serverAck: (client) ->
        throw new Error("There is no pending operation.")

      transformAnnotation: (annotation) ->
        annotation
    
    class AwaitingConfirm
      constructor: (operation,annotation) ->
        @operation = operation

      applyClient: (client, operation) ->
        new AwaitingWithBuffer(@operation, operation)

      applyClientAnnotation: (client, annotation) ->
        

      applyServer: (client, operation, annotation) ->
        if operation?
          pair = operation.constructor.transform(@operation, operation)
          client.applyOperation pair[1]
          return new AwaitingConfirm(pair[0])
        else if @operation and annotation?
          annon = annotation.constructor.transform(annotation,@operation)
          client.applyAnnotation(annon)
          return this

      serverAck: (client) -> new Synchronized

      transformAnnotation: (annotation) ->
        annotation.transform @operation

      resend: (client) ->
        client.sendOperation client.revision, @operation

    class AwaitingWithBuffer 
      constructor: (operation, buffer) ->
        @operation = operation        
        @buffer      = buffer        

      applyClient: (client, operation) ->        
        # Compose the user's changes onto the buffer
        newBuffer = @buffer.compose(operation)
        new AwaitingWithBuffer(@operation, newBuffer)

      applyClientAnnotation: (client, annotation) -> 


      applyServer: (client, operation, annotation) ->
        transform = operation.constructor.transform
        pair1 = transform(@operation, operation)
        pair2 = transform(@buffer, pair1[1])
        client.applyOperation pair2[1]
        new AwaitingWithBuffer(pair1[0], pair2[0])

      serverAck: (client) ->
        client.sendOperation client.revision, @buffer
        new AwaitingConfirm(@buffer)

      transformAnnotation: (annotation) ->
        annotation.transform(@operation).transform @buffer

      resend: (client) ->
        client.sendOperation client.revision, @operation