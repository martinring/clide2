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

    serverAck: ->
      @revision++
      @setState @state.serverAck(this)

    serverReconnect: ->
      @state.resend? this

    transformAnnotation: (annotation) ->
      @state.transformAnnotation annotation

    sendAnnotation: (revision, annotation) ->
      throw new Error("sendAnnotation must be defined in child class")

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

      annotate: (client, annotation) ->
        client.annotation = null
        if client.annotationTimeout?
          client.annotation = annotation
        else
          client.sendAnnotation client.revision, annotation
          client.setAnnotationTimeout()

      transformAnnotation: (annotation) ->
        annotation
    
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
        if not client.annotationTimeout? and client.annotation?
          client.sendAnnotation client.revision, client.annotation
          client.annotation = null
          client.setAnnotationTimeout()
        new Synchronized

      annotate: (client, annotation) ->
        client.annotation = annotation

      transformAnnotation: (annotation) ->
        annotation.transform @outstanding

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
        if not client.annotationTimeout? and client.annotation?
          client.sendAnnotation client.revision, client.annotation
          client.annotation = null
          client.setAnnotationTimeout()
        new AwaitingConfirm(@buffer)

      annotate: (client, annotation) ->
        client.annotation = annotation

      transformAnnotation: (annotation) ->
        annotation.transform(@outstanding).transform @buffer

      resend: (client) ->
        client.sendOperation client.revision, @outstanding