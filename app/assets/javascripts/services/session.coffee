### @service services:Session ###
define ['routes'], (routes) -> ($q,$http,$timeout,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  
  
  session =
    state: 'closed'
    collaborators: null
    openFiles: null
    activeFile: null
    me: null

  remove = (id) ->
    for s, i in session.collaborators
      if s.id is id
        return session.collaborators.splice(i,1)

  update = (info) ->
    for s, i in session.collaborators
      if s.id is info.id        
        for k, v of info          
          session.collaborators[i][k] = v
        return true
    session.collaborators.push(info)
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.session(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    socket = ws
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      switch typeof msg
        when 'string'
          switch msg
            when 'ack'
              console.log 'ack'
            else
              Toasts.push 'danger', "internal error: unknown message: #{msg}"
        when 'array'
          console.log 'edit'
        when 'object'
          switch msg.t
            when 'e'
              Toasts.push 'danger', msg.c
            when 'welcome'              
              session.openFiles = msg.openFiles
              session.activeFile = msg.activeFile            
              $timeout ->
                session.me = msg.info
                session.collaborators = msg.others
            when 'opened'
              session.openFiles.push(msg.c)            
              session.activeFile = msg.c.info.id
              $timeout ->            
                session.activeFile = msg.c.info.id #TODO: HACK
            when 'close'
              $timeout ->
                for f, i in session.openFiles
                  if f.info.id is msg.c
                    return session.openFiles.splice(i,1)
                session.activeFile = null
            when 'switch'
              session.activeFile = msg.c
              $timeout -> 
                session.activeFile = msg.c
            when 'session_changed'
              $timeout ->
                update(msg.c)
            when 'session_stopped'
              $timeout ->
                remove(msg.c.id)
    ws.onopen = (e) ->
      $timeout -> session.state = 'connected'
      console.log 'opened'
      for msg in queue
        console.log 'sending: ', JSON.stringify(msg)
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->
      $timeout -> session.state = 'disconnected'
      socket = undefined
      console.log e

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))        
    when WebSocket.OPEN      
      console.log message
      data = JSON.stringify(message)
      socket.send(data)      

  return (
    getOpenFile: (id) ->
      for file in session.openFiles
        if file.info.id is id
          return file
      return false
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
    edit: (id,rev,actions) ->
      if (id isnt session.activeFile)
        Toast.push 'danger', 'internal error: edit inactive file (todo)'
      else send
        r: rev
        o: actions
    leave: ->
      socket.close()
  )