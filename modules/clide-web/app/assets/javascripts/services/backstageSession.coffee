### @service services:BackstageSession ###
define ['routes'], (routes) -> ($q,$rootScope,$http,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  

  session =
    state: 'closed'
    projects: null
    otherProjects: null

  apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f)

  get = (username, init) ->
    ws = new WebSocket(pc.backstageSession(username).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    socket = ws
    apply -> 
      session.state = 'connecting'
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      switch typeof msg        
        when 'object'        
          if msg.f? and msg.o?
            getOpenFile(msg.f).$apply(Operation.fromJSON(msg.o))
          switch msg.t
            when 'projects'
              apply ->
                session.projects = msg.c.own
                session.otherProjects = msg.c.other            
            when 'access'
              apply ->
                session.otherProjects = session.otherProjects.filter((p) -> p.id isnt msg.c.p.id)
                if msg.c.l > 0
                  session.otherProjects.push(msg.c.p)
            when 'createdproject'
              apply ->
                if msg.c.owner is username
                  session.projects.push(msg.c)
                else
                  session.otherProjects.push(msg.c)
            when 'deletedproject'
              apply ->                
                session.projects = session.projects.filter((p) -> p.id isnt msg.c)                
                session.otherProjects = session.otherProjects.filter((p) -> p.id isnt msg.c)
    ws.onopen = (e) ->
      apply -> session.state = 'connected'      
      for msg in queue        
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->
      socket = undefined
      session.projects = null
      session.otherProjects = null
      apply -> session.state = 'disconnected'

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))        
    when WebSocket.OPEN      
      data = JSON.stringify(message)
      socket.send(data)      

  return (    
    info: session      
    init: (username, init) ->
      socket or get(username, init)
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