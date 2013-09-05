### @service services:Session ###
define ['routes'], (routes) -> ($q,$http,$timeout) ->
  pc = routes.clide.web.controllers.Projects
  
  current   = undefined
  listeners = undefined

  traffic = {
    in: 0
    out: 0
  }

  get = (username, project) ->
    ws = new WebSocket(pc.session(username,project).webSocketURL())
    listeners = { }
    current = ws
    ws.onmessage = (e) ->
      $timeout((->traffic.in += e.data.length),0)
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      if msg.path?
        listeners[msg.path]?(msg)
      else if msg.error?        
        console.error msg.error
    ws.onclose = (e) ->
      listeners = undefined
      current = undefined
      traffic.in = 0
      traffic.out = 0
      console.log 'socket closed'

  return (
    traffic: traffic
    open: (username, project) ->
      current or get(username, project)            
    close: ->
      current.close()
    listen: (path, callback) ->      
      listeners[path] = callback
    ignore: (path) ->
      listeners[path] = undefined
    send: (message) ->
      data = JSON.stringify(message)      
      $timeout((->traffic.out += data.length),0)
      console.log "sending: ", data
      current.send(data)
  )