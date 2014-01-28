##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU Lesser General Public License as           ##
##   published by the Free Software Foundation, either version 3 of           ##
##   the License, or (at your option) any later version.                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU Lesser General Public         ##
##   License along with Clide.                                                ##
##   If not, see <http://www.gnu.org/licenses/>.                              ##
##                                                                            ##

### @service services:Session ###
define ['routes','util/actorSocket','collaboration/Operation','collaboration/CodeMirror','collaboration/Client','collaboration/Annotations','modes/isabelle/defaultWords','codemirror'], (routes,ActorSocket,Operation,CMAdapter,Client,Annotations,idw,CodeMirror) -> ($q,$rootScope,$http,Toasts,Dialog) ->
  (username, project) ->
    session =
      state: 'closed'
      collaborators: null
      openFiles: null
      talkback: null
      kicked: null
      fileStates: { }
      chat: []
      me: null

    session.activeDoc = ->
      session.openFiles?[session.me.activeFile]?.doc

    session.activeAnnotations = ->
      session.openFiles?[session.me.activeFile]?.annotations

    session.syncState = ->
      session.openFiles?[session.me.activeFile]?.$syncState()

    apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f) else f()

    setActiveFile = (id,send) ->
      if session.me.activeFile? then send
        t: 'ignoring'
        f: session.me.activeFile
      session.me.activeFile = id
      if id? then send
        t: 'looking'
        f: id

    initFile = (file, send) ->
      nfile = session.openFiles[file.info.id] or { }

      nfile.id   = file.info.id
      nfile.name = file.info.name

      if nfile.doc?
        nfile.doc.setValue(file.state)
      else
        if file.info.mimeType is 'text/isabelle'
          nfile.doc  = CodeMirror.Doc file.state,
            name: 'isabelle'
            words: idw
        else
          nfile.doc = CodeMirror.Doc file.state, (file.info.mimeType or 'text/plain')

      client  = new Client(file.revision)
      adapter = new CMAdapter(nfile.doc, session.me.color)

      client.applyOperation = adapter.applyOperation
      reset = () ->
        console.warning('warning', 'emergency resetting ' + nfile.name + ' due to server timeout')
        nfile.$$emergencyResetMode = true
        send
          t: 'close'
          id: file.info.id
        send
          t: 'open'
          id: file.info.id
      client.sendOperation = (rev,op) ->
        nfile.$$emergencyReset = setTimeout(reset, 1000)
        send
          f: nfile.id
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

      nfile.$ackEdit = () ->
        clearTimeout(nfile.$$emergencyReset)
        client.serverAckEdit()
      nfile.$ackAnnotation = () -> client.serverAckAnnotation()
      nfile.$apply = (os) -> client.applyServer(os)
      nfile.$syncState = -> client.syncState()
      nfile.$setColor = (c) -> adapter.setColor(c)
      nfile.$annotate = (a,u,n) ->
        nfile.annotations          = nfile.annotations or { }
        nfile.annotations[u.id]    = nfile.annotations[u.id] or [ ]
        s = null
        for stream in nfile.annotations[u.id]
          if stream.name is n
            s = stream
            break
        unless s?
          s = { show: true, name: n }
          nfile.annotations[u.id].push s
        s.show = true
        a = client.transformAnnotation(a)
        adapter.applyAnnotation(a,u,n)
      nfile.$addAnnotations = (u,n,d) ->
        nfile.annotations    = nfile.annotations or { }
        nfile.annotations[u] = nfile.annotations[u] or [ ]
        for stream in nfile.annotations[u]
          if stream.name is n
            stream.description = d
            return
        nfile.annotations[u].push { show: false, name: n, description: d }
      nfile.$removeAnnotations = (u,n) ->
        nfile.annotations    = nfile.annotations or { }
        nfile.annotations[u] = nfile.annotations[u] or [ ]
        for stream in nfile.annotations[u]
          if stream.name is n
            stream.show = false
            break
        adapter.resetAnnotations(u,n)
      if (nfile.$$emergencyResetMode)
        nfile.$$emergencyResetMode = false
        console.log 'resetted ' + nfile.name

      session.openFiles[file.info.id] = (nfile)

    getOpenFile = (id) -> session.openFiles[id] or false

    remove = (id) ->
      for s, i in session.collaborators
        if s.id is id
          s.active = false
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

    url = routes.clide.web.controllers.Projects.session(username, project).webSocketURL()
    new ActorSocket url, "#{username}/#{project}/session", (context) ->
      data: session
      interface:
        openFile: (id) -> unless id is session.me.activeFile
          existing = getOpenFile(id)
          if existing
            setActiveFile(id,context.tell)
          else context.tell
            t: 'open'
            id: id
        closeFile: (id) ->
          apply ->
            delete session.openFiles[id]
            setActiveFile(null,context.tell)
          context.tell
            t: 'close'
            id: id
        chat: (msg) ->
          context.tell
            t:   'chat'
            msg: msg
        invite: (name) ->
          context.tell
            t: 'invite'
            u: name
        kick: (id) ->
          context.tell
            t: 'kick'
            s: id
        subscribe: (file, user, name) ->
          context.tell
            t: 'subscribe'
            f: file
            u: user
            n: name
        unsubscribe: (file, user, name) ->
          context.tell
            t: 'unsubscribe'
            f: file
            u: user
            n: name
        setColor: (color) ->
          session.me.color = color
          for key, file of session.openFiles
            file.$setColor?(color)
          #document.getElementById('theme').href = "/client/stylesheets/colors/#{color}.css"
          context.tell
            t: 'color'
            c: color
        hints: (cm, options) -> undefined
        close: ->
          queue = []
          context.tell
            t: 'eof'
          socket?.close()
      preStart: ->
        session.state = 'connected'
        context.setReceiveTimeout 100
        context.tell { t: 'init' }
        CodeMirror.registerHelper "hint", (e...) ->
          return (
            showHint: () -> console.log 'hn'
          )
            getOpenFile: getOpenFile
      receive: (msg) ->
        silence = false
        f = (msg) -> switch typeof msg
          when 'number'
            f = getOpenFile(msg)
            if f
              f.$ackEdit()
            else
              log.warning("acknowledge for unknown file " + msg)
          when 'object'
            if msg.f? and msg.o?
              getOpenFile(msg.f).$apply(Operation.fromJSON(msg.o))
            else if msg.f? and msg.a? and (user = getUser(msg.u))?
              apply ->
                getOpenFile(msg.f).$annotate(Annotations.fromJSON(msg.a),user,msg.n)
            switch msg.t
              when 'timeout'
                context.tell { t: 'flush', blowup: [1..1000] }
              when 'e'
                Toasts.push 'danger', msg.c
              when 'welcome'
                context.setReceiveTimeout null
                session.openFiles = { }
                #document.getElementById('theme').href = "/client/stylesheets/colors/#{msg.info.color}.css"
                apply ->
                  session.me = msg.info
                  session.collaborators = msg.others
                silence = true
                f(event) for event in msg.events.reverse()
                silence = false
              when 'kicked'
                (apply -> session.kicked?())
              when 'opened'
                apply ->
                  initFile(msg.c, context.tell)
                  setActiveFile(msg.c.info.id, context.tell)
              when 'failed'
                Toasts.push("danger","the initialization of the requested file failed on the server")
              when 'ao'
                apply ->
                  getOpenFile(msg.f).$addAnnotations(msg.u,msg.n,msg.d)
              when 'ac'
                apply ->
                  getOpenFile(msg.f).$removeAnnotations(msg.u,msg.n)
              when 'talk'
                if msg.c.s is session.me.id
                  msg.c.s = session.me
                else
                  msg.c.s = getUser(msg.c.s)
                session.chat.unshift(msg.c)
                (apply -> session.talkback?(msg.c)) unless silence
              when 'close'
                console.log 'close file acknowledged'
              when 'session_changed'
                apply ->
                  update(msg.c)
              when 'session_stopped'
                apply ->
                  remove(msg.c.id)
              when 'process'
                f = ->
                  session.fileStates[msg.c.f] = session.fileStates[msg.c.f] or {}
                  session.fileStates[msg.c.f][msg.c.u] = session.fileStates[msg.c.f][msg.c.u] or {}
                  switch msg.c.t
                    when 'w'
                      session.fileStates[msg.c.f][msg.c.u].working = true
                    when 'd'
                      session.fileStates[msg.c.f][msg.c.u].working = false
                    when 'l'
                      session.fileStates[msg.c.f][msg.c.u].looking = true
                    when 'i'
                      session.fileStates[msg.c.f][msg.c.u].looking = false
                if silence
                  f()
                else
                  apply f

        f(msg)
