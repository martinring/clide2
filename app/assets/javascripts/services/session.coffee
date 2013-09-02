### @service services:Session ###
define ['routes'], (routes) -> ($q,$http) ->
  pc = routes.controllers.Projects
  
  current   = undefined
  listeners = undefined

  get = (username, project) ->
    ws = new WebSocket(pc.session(username,project).webSocketURL())
    listeners = { }
    current = ws
    ws.onmessage = (e) ->      
      msg = JSON.parse(e.data)      
      console.log msg
      if msg.path?
        listeners[msg.path]?(msg)
      else if msg.error?        
        console.error msg.error
    ws.onclose = (e) ->
      listeners = undefined
      current = undefined
      console.log 'socket closed'

  return (    
    open: (username, project) ->
      current or get(username, project)            
    close: ->
      current.close()    
    listen: (path, callback) ->      
      listeners[path] = callback
    ignore: (path) ->
      listeners[path] = undefined
    send: (message) ->
      console.log message
      console.log current
      current.send(JSON.stringify(message))
  )