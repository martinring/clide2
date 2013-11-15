define ->
  class ActorSocket
    constructor: (@url,@name) ->
      @socket = new WebSocket(@url)

      inbox  = []
      outbox = []

      @preStart()

      receiveTimeoutSpan = undefined
      receiveTimeout     = undefined
      onTimeout = () ->
        @receive
          t: 'timeout'
      @setReceiveTimeout = (ms) ->
        receiveTimeoutSpan = ms
      resetTimeout = () ->
        clearTimeout(receiveTimeout)
        if receiveTimeoutSpan?
          setTimeout(onTimeout,receiveTimeoutSpan)

      @socket.onmessage = (e) ->
        resetTimeout()
        console.log "actor '#{@name}' received: #{e.data}"
        msg = JSON.parse(e.data)
        try
          @receive(msg)
        catch error
          console.error error

      @socket.onerror = (e) ->
        console.error error

      @socket.onclose = () ->
        @receive
          t: 'terminated'

      @socket.onopen = () ->
        for msg in outbox
          @socket.send(msg)

      @peer =
        tell: (msg) ->
          data = JSON.stringify(msg)
          if @socket.readyState is WebSocket.OPEN
            @socket.send(data)
          else
            outbox.push(data)
          resetTimout()

    preStart: () ->
      # may be overridden

    postStop: () ->
      # may be overridden

    receive: (msg) ->
      throw new Error('receive must be defined in child class')
