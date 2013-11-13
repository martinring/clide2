define -> class ActorSocket
  constructor: (@url) ->
    @socket = new WebSocket(@url)
    @mailbox = []
    @socket.onmessage = (e) ->
      msg = JSON.parse(e.data)
      @receive(msg)

  receive: (msg) ->
    throw new Error('receive must be defined in child class')
