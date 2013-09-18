### @service services:Session ###
define ['routes'], (routes) -> ($q,$http,$timeout,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  

  session =
    collaborators: null
    openFiles: null
    activeFiles: null
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
      switch msg.t
        when 'e'
          Toasts.push 'danger', msg.c
        when 'welcome'
          $timeout((->
            session.me = msg.info
            session.collaborators = msg.others
            session.openFiles = msg.openFiles
            session.activeFile = msg.activeFile),0)
        when 'session_changed'
          $timeout((->update(msg.c)),0)
        when 'session_stopped'
          $timeout((->remove(msg.c.id)),0)
    ws.onopen = (e) ->
      console.log 'opened'
      for msg in queue
        console.log 'sending: ', JSON.stringify(msg)
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->
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
    info: session
    init: (username, project, init) ->
      socket or get(username, project, init)
      send 
        t: 'init'
    create: (path) -> send
      t: 'new'
      path: path or dirs[currentdir].info.path or []
    leave: ->
      socket.close()
  )