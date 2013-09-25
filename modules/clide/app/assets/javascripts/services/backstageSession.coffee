### @service services:BackstageSession ###
define ['routes'], (routes) -> ($q,$rootScope,$http,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  

  session =
    state: 'closed'
    collaborators: null
    openFiles: null
    activeFileId: null
    me: null

  apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f)

  get = (username, project, init) ->
    ws = new WebSocket(pc.session(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    socket = ws
    apply -> 
      session.state = 'connecting'
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      switch typeof msg
        when 'string'
          switch msg
            when 'ack'
              getOpenFile(session.activeFileId).$ack()
            else
              Toasts.push 'danger', "internal error: unknown message: #{msg}"        
        when 'object'        
          if msg.f? and msg.o?
            getOpenFile(msg.f).$apply(Operation.fromJSON(msg.o))
          switch msg.t
            when 'e'
              Toasts.push 'danger', msg.c
            when 'welcome'
              session.openFiles = { }
              apply ->
                session.me = msg.info
                session.collaborators = msg.others
            when 'opened'
              apply -> initFile(msg.c)
            when 'close'
              apply ->                
                delete session.openFiles[msg.c]
                session.activeFileId = null
            when 'switch'
              apply ->
                session.activeFileId = msg.c
            when 'session_changed'
              apply ->
                update(msg.c)
            when 'session_stopped'
              apply ->
                remove(msg.c.id)
    ws.onopen = (e) ->
      apply -> session.state = 'connected'
      console.log 'opened'
      for msg in queue
        console.log 'sending: ', JSON.stringify(msg)
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->      
      socket = undefined        
      session.collaborators = null
      session.openFiles = null
      session.activeFileId = null
      session.me = null
      apply -> session.state = 'disconnected'
      console.log e

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))        
    when WebSocket.OPEN      
      console.log message
      data = JSON.stringify(message)
      socket.send(data)      

  return (
    getOpenFile: getOpenFile    
    info: session      
    init: (username, project, init) ->
      socket or get(username, project, init)
      send 
        t: 'init'
    openFile: (id) -> send
      t: 'open'
      id: id
    closeFile: (id) -> send
      t: 'close'
      id: id
    close: ->
      queue = []
      socket?.close()
  )