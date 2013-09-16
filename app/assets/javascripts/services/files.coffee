### @service services:Files ###
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects
  
  current   = undefined
  listeners = undefined

  currentdir = {
    
  }
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.fileBrowser(username,project).webSocketURL())
    listeners = { }
    current = ws
    ws.onmessage = (e) ->      
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      if msg.path?
        listeners[msg.path]?(msg)
      else if msg.error?
        console.error msg.error
    ws.onopen = (e) ->
      console.log 'sending: ', JSON.stringify(init)
      ws.send(JSON.stringify(init)) if init?
    ws.onclose = (e) ->
      listeners = undefined
      current = undefined
      console.log e

  return (
    open: (username, project, init) ->
      current or get(username, project, init)            
    close: ->
      current.close()
    listen: (path, callback) ->      
      listeners[path] = callback
    ignore: (path) ->
      listeners[path] = undefined
    send: (message) ->
      data = JSON.stringify(message)
      console.log "sending: ", data
      current.send(data)    
  )