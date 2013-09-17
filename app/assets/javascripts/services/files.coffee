### @service services:Files ###
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects
  
  socket  = undefined
  dirs = { }
  currentdir = -1
  queue = []
  selections = { }
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.fileBrowser(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?    
    socket= ws
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      switch msg.t
        when 'e'
          Toasts.push 'danger', msg.c      
        when 'newfile'
          f = -> dirs[msg.c.parent]?.files.push msg.c
          if msg.c.parent is currentdir
            $timeout f, 0
          else f()
        when 'rmfile'
          f = ->          
            if dirs[msg.c.parent]?              
              for file, j in dirs[msg.c.parent].files
                if file.id is msg.c.id
                  dirs[msg.c.parent].files.splice(j,1)
                  return
          if msg.c.parent is currentdir
            $timeout f, 0
          else f()
        when 'folder'
          path = [{name: '$home', path: []}]
          for segment, i in msg.info.path
            p = path[i].path.slice()
            p.push(segment)
            path.push
              name: segment
              path: p
          $timeout((->            
            dirs[msg.info.id] = 
              info: msg.info
              path: path
              files: msg.files              
            currentdir = msg.info.id
            console.log dirs[currentdir]),0)
    ws.onopen = (e) ->      
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
    current: -> dirs[currentdir]
    selections: selections
    init: (username, project, init) ->
      socket or get(username, project, init)
    explore: (path) -> send
      t: 'explore'
      path: path
    browseTo: (path) -> send
      t: 'browse'
      path: path
    touchFile: (path) -> send
      t: 'touchFile'
      path: path
    touchFolder: (path) -> send
      t: 'touchFolder'
      path: path
    open: (path) -> send
      t: 'open'
      path: path
    select: (path) -> send
      t: 'select'
      path: path
    delete: (path) -> send
      t: 'rm'
      path: path
    create: (path) -> send
      t: 'new'
      path: path or dirs[currentdir].info.path or []
    leave: ->
      socket.close()
  )