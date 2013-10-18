### @service services:Session ###
define ['routes','collaboration/Operation','collaboration/CodeMirror','collaboration/Client','collaboration/Annotations','modes/isabelle/defaultWords','codemirror'], (routes,Operation,CMAdapter,Client,Annotations,idw,CodeMirror) -> ($q,$rootScope,$http,Toasts) ->
  pc = routes.clide.web.controllers.Projects

  queue = []
  socket  = undefined  

  session =
    state: 'closed'
    collaborators: null
    openFiles: null
    talkback: null
    chat: []
    me: null

  session.activeDoc = ->
    session.openFiles?[session.me.activeFile]?.doc

  session.syncState = ->
    session.openFiles?[session.me.activeFile]?.$syncState()

  apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f) else f()

  initFile = (file) ->
    nfile = session.openFiles[file.info.id] or { }

    nfile.id   = file.info.id
    nfile.name = file.info.name        
    if file.info.mimeType is 'text/isabelle'  
      console.log 'true'
      nfile.doc  = CodeMirror.Doc file.state,
        name: 'isabelle'
        words: idw
    else
      nfile.doc = CodeMirror.Doc file.state, (file.info.mimeType or 'text/plain')    

    client  = new Client(file.revision)
    adapter = new CMAdapter(nfile.doc, session.me.color)        

    client.applyOperation = adapter.applyOperation
    client.sendOperation = (rev,op) -> send
        f: nfile.id # TODO: handle on server!
        r: rev
        o: op.actions
    client.sendAnnotation = (rev,an,name) -> send
        f: nfile.id
        r: rev
        a: an.annotations
        n: name

    adapter.registerCallbacks
      change: (op) -> client.applyClient(op)
      annotate: (a) -> client.annotate(a)

    nfile.$ackEdit = () -> client.serverAckEdit()
    nfile.$ackAnnotation = () -> client.serverAckAnnotation()
    nfile.$apply = (os) -> client.applyServer(os)
    nfile.$syncState = -> client.syncState()
    nfile.$setColor = (c) -> adapter.setColor(c)
    nfile.$annotate = (a,u,n) -> # TODO: include user
      a = client.transformAnnotation(a)
      adapter.applyAnnotation(a,u,n)
    
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

  getUser = (id) ->
    for s in session.collaborators
      if s.id is id
        return s
    return null    
  
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
            when 'ack_edit'
              getOpenFile(session.me.activeFile).$ackEdit()
            when 'ack_annotate'
              getOpenFile(session.me.activeFile).$ackAnnotation()
            else
              Toasts.push 'danger', "internal error: unknown message: #{msg}"        
        when 'object'        
          if msg.f? and msg.o?
            getOpenFile(msg.f).$apply(Operation.fromJSON(msg.o))
          else if msg.f? and msg.a?
            user = null            
            getOpenFile(msg.f).$annotate(Annotations.fromJSON(msg.a),getUser(msg.u),msg.n)
          switch msg.t
            when 'e'
              Toasts.push 'danger', msg.c
            when 'welcome'
              session.openFiles = { }              
              #document.getElementById('theme').href = "/client/stylesheets/colors/#{msg.info.color}.css"
              apply ->
                session.me = msg.info
                session.collaborators = msg.others
                session.chat = msg.chat.reverse()
            when 'opened'
              apply -> initFile(msg.c)
            when 'failed'
              Toasts.push("danger","the initialization of the requested file failed on the server")
            when 'talk'              
              apply ->
                session.talkback?(msg.c)
                session.chat.unshift(msg.c)
            when 'close'
              apply ->                
                delete session.openFiles[msg.c]
                session.me.activeFile = null
            when 'switch'
              apply ->                
                session.me.activeFile = msg.c                                            
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
    ws.onclose = ws.onerror = (e) ->      
      socket = undefined        
      session.collaborators = null
      session.openFiles = null
      session.me.activeFile = null
      session.me = null
      session.chat = []
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
    openFile: (id) -> unless session.me.activeFile is id
      send
        t: 'open'
        id: id
    closeFile: (id) -> 
      send
        t: 'close'
        id: id
    chat: (msg) ->
      send
        t:   'chat'
        msg: msg
    invite: (name) -> 
      send
        t: 'invite'
        u: name
    setColor: (color) -> 
      session.me.color = color
      for key, file of session.openFiles
        file.$setColor?(color)

      #document.getElementById('theme').href = "/client/stylesheets/colors/#{color}.css"
      send
        t: 'color'
        c: color
    close: ->
      queue = []
      socket?.close()
  )