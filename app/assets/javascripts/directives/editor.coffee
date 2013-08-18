### @directive directives:editor ###
define ['codemirror','routes','concurrency/Client','concurrency/CodeMirrorAdapter'], (CodeMirror,routes,Client,CMAdapter) -> () -> 
  restrict: 'E'
  transclude: true
  controller: ($scope, $element) ->
    null
  template: '<textarea ng-transclude></textarea>'
  replace: true
  link: (scope, iElem, iAttrs, controller) ->    
    cm = CodeMirror.fromTextArea iElem[0],
      lineNumbers: true
      readOnly: true
      undoDepth: 0 # disable

    socket = new WebSocket(routes.controllers.Application.collab().webSocketURL())

    client = null

    socket.onmessage = (e) -> 
      msg = JSON.parse(e.data)
      switch msg.type
        when 'registered'
          console.log "successfully registerd as client #{msg.id}"
          doc = new Document
          client = new Client(msg.id, doc)
          client.registerCallbacks
            insert: (e) -> 
              console.log e
            hide: (e) -> 
              console.log e          
          cm.setOption('readOnly',false)
          cm.on "beforeChange", (cm, change) ->
            index = cm.indexFromPos(change.from)
            text = change.text.join '\n'
            if change.from isnt change.to
              console.log "user deleted letter at #{index}"
              del = client.generateHide(index)
              client.applyOperation(del)
            else if text.length > 0
              console.log "user inserted letter '#{text}' at #{index}"
              ins = client.generateInsert(index,text)                        
              client.applyOperation(ins)
              socket.send JSON.stringify(ins)                
        when 'error'
          alert(msg.msg)
        else 
          console.log 'server: ', msg
          if client.canApplyOperation(msg)
            client.applyOperation(msg)
          else 
            alert('preconditions unfulfilled')

    socket.onopen = ->
      socket.send JSON.stringify
        type: 'register'

    socket.onclose = ->
      console.log 'connection lost'