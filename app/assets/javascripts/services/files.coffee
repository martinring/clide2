### @service services:Files ###
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects
  
  current   = undefined
  currentdir = { }
  queue = []
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.fileBrowser(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    listeners = { }
    current = ws
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      switch msg.t
        when 'newfile'
          if msg.c.parent is currentdir.info.id
            $timeout((->currentdir.files.push(msg.c)),0)
        when 'folder'
          path = [{name: '$home', path: []}]
          for segment, i in msg.info.path
            p = path[i].path.slice()
            p.push(segment)
            path.push
              name: segment
              path: p
          $timeout((->
            currentdir.info = msg.info
            currentdir.path = path
            currentdir.files = msg.files),0)
    ws.onopen = (e) ->      
      for msg in queue
        console.log 'sending: ', JSON.stringify(msg)
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->
      listeners = undefined
      current = undefined
      console.log e

  return (
    current: currentdir
    open: (username, project, init) ->
      current or get(username, project, init)
    close: ->
      current.close()
    send: (message) -> switch current?.readyState
      when WebSocket.CONNECTING
        queue.push(JSON.stringify(message))        
      when WebSocket.OPEN      
        console.log message
        data = JSON.stringify(message)
        current.send(data)      
  )