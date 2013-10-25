### @service services:Files ###
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects
  
  socket  = undefined
  dirs = []
  queue = []

  currentDirId = null

  files =
    currentDir: null
    state: 'closed'
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.fileBrowser(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?    
    socket= ws
    $timeout((-> files.state = 'connecting'),0)
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)      
      switch msg.t
        when 'e'
          Toasts.push 'danger', msg.c
        when 'newfile'
          f = -> dirs[msg.c.parent]?.files.push msg.c
          if msg.c.parent is currentDirId
            $timeout f, 0
          else f()
        when 'rmfile'        
          f = ->            
            if dirs[msg.c.parent]?
              for file, j in dirs[msg.c.parent].files
                if file.id is msg.c.id
                  dirs[msg.c.parent].files.splice(j,1)
                  return
          if msg.c.parent is currentDirId
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
            currentDirId = msg.info.id
            files.currentDir = dirs[currentDirId]),0)
    ws.onopen = (e) ->      
      $timeout((-> files.state = 'connected'),0)
      for msg in queue        
        ws.send(msg)
      queue = []      
    ws.onclose = ws.onerror = (e) ->
      listeners = undefined
      socket = undefined
      $timeout((-> files.state= 'disconnected'),0)

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))        
    when WebSocket.OPEN            
      data = JSON.stringify(message)
      socket.send(data)      

  return (
    info: files
    init: (username, project, init) ->
      socket or get(username, project, init)
    explore: (path) -> send
      t: 'explore'
      path: path
    browseTo: (path,id) -> send
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
      path: path or dirs[currentDirId].info.path or []
    close: ->
      socket?.close()
  )