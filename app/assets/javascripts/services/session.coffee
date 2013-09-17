### @service services:Session ###
define ['routes'], (routes) -> ($q,$http,$timeout,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined
  me = null
  collaborators = null

  remove = (id) ->
    for session, i in collaborators
      if session.id is id
        return collaborators.splice(i,1)

  update = (info) ->
    for session, i in collaborators
      if session.id is info.id
        console.log 'updating', info, i
        for k, v of info          
          collaborators[i][k] = v
        return true
    collaborators.push(info)
  
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
            me = msg.info
            collaborators = msg.others),0)
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
      listeners = undefined
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
    me: -> me
    collaborators: -> collaborators
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