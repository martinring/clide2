### @service services:Session ###
define ['routes','collab/Operation','collab/CodeMirror','collab/Client','collab/AnnotationStream','modes/isabelle/defaultWords'], (routes,Operation,CMAdapter,Client,AnnotationStream,idw) -> ($q,$rootScope,$http,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  

  session =
    state: 'closed'
    collaborators: null
    openFiles: null
    activeFileId: null
    me: null

  session.activeDoc = ->
    session.openFiles?[session.activeFileId]?.doc

  apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f) else f()

  initFile = (file) ->
    nfile = session.openFiles[file.info.id] or { }

    nfile.id   = file.info.id
    nfile.name = file.info.name  
    nfile.doc  = CodeMirror.Doc file.state,
      name: 'isabelle'
      words: idw
    
    client  = new Client(file.revision)
    adapter = new CMAdapter(nfile.doc)

    client.applyOperation = adapter.applyOperation
    client.sendOperation  = (rev,op) ->
      if (nfile.id isnt session.activeFileId)
        Toast.push 'danger', 'internal error: edit inactive file (todo)'
      else send
        r: rev
        o: op.actions

    adapter.registerCallbacks
      change: (op) -> client.applyClient(op)

    nfile.$ack   = () -> client.serverAck()
    nfile.$apply = (os) -> client.applyServer(os)

    unless session.openFiles[file.info.id]?
      session.openFiles[file.info.id] = (nfile)

    console.log session.openFiles

  getOpenFile = (id) -> session.openFiles[id] or false    

  remove = (id) ->
    for s, i in session.collaborators
      if s.id is id
        return session.collaborators.splice(i,1)

  update = (info) ->
    for s, i in session.collaborators
      if s.id is info.id        
        for k, v of info          
          session.collaborators[i][k] = v
        session.collaborators[i].activeFile = info.activeFile
        return true
    session.collaborators.push(info)
  
  get = (username, project, init) ->
    ws = new WebSocket(pc.session(username,project).webSocketURL())
    queue.push(JSON.stringify(init)) if init?
    socket = ws
    apply -> 
      session.state = 'connecting'
    ws.onmessage = (e) ->
      msg = JSON.parse(e.data)
      console.log "received: ", e.data
      switch typeof msg
        when 'string'
          switch msg
            when 'ack'
              getOpenFile(session.activeFileId).$ack()
            else
              Toasts.push 'danger', "internal error: unknown message: #{msg}"        
        when 'object'        
          if msg.f? and msg.o?
            getOpenFile(msg.f).$apply(Operation.fromJSON(msg.o))
          switch msg.t
            when 'e'
              Toasts.push 'danger', msg.c
            when 'welcome'
              session.openFiles = { }              
              document.getElementById('theme').href = "/client/stylesheets/colors/#{msg.info.color}.css"
              apply ->
                session.me = msg.info
                session.collaborators = msg.others
            when 'opened'
              apply -> initFile(msg.c)
            when 'close'
              apply ->                
                delete session.openFiles[msg.c]
                session.activeFileId = null
            when 'switch'
              apply ->
                session.activeFileId = msg.c
            when 'session_changed'
              apply ->
                update(msg.c)
            when 'session_stopped'
              apply ->
                remove(msg.c.id)
    ws.onopen = (e) ->
      apply -> session.state = 'connected'
      console.log 'opened'
      for msg in queue
        console.log 'sending: ', JSON.stringify(msg)
        ws.send(msg)
      queue = []
    ws.onclose = (e) ->      
      socket = undefined        
      session.collaborators = null
      session.openFiles = null
      session.activeFileId = null
      session.me = null
      apply -> session.state = 'disconnected'
      console.log e

  send = (message) -> switch socket?.readyState
    when WebSocket.CONNECTING
      queue.push(JSON.stringify(message))        
    when WebSocket.OPEN      
      console.log message
      data = JSON.stringify(message)
      socket.send(data)      

  return (
    getOpenFile: getOpenFile    
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
    setColor: (color) -> 
      session.me.color = color
      document.getElementById('theme').href = "/client/stylesheets/colors/#{color}.css"
      send
        t: 'color'
        c: color
    close: ->
      queue = []
      socket?.close()
  )