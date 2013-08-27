### @directive directives:editor ###
define ['codemirror','routes','collab/Operation','collab/CodeMirror','collab/Client','collab/Annotations'], (CodeMirror,routes,Operation,CMAdapter,Client,Annotations) -> (Dialog,$timeout) -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],
      lineNumbers: true
      #readOnly: true
      undoDepth: 0 # disable
      placeholder: 'content loading...'

    scope.$watch (-> scope.$eval(iAttrs.file)), (n,o) -> if n?
      unless o?
        $timeout((-> cm.refresh()),0)
      cm.focus()
      unless n.doc?
        n.doc = CodeMirror.Doc('content loading...')
      cm.swapDoc(n.doc)

    #socket = new WebSocket(routes.controllers.Application.collab().webSocketURL())
    socket = {}

    client = null
    annotations = new Annotations

    socket.onmessage = (e) -> 
      msg = JSON.parse(e.data)
      switch msg.type
        when 'init'
          cm.setValue(msg.doc)
          client = new Client(msg.rev)
          adapter = new CMAdapter(cm)
          client.sendOperation = (revision, operation) ->
            socket.send JSON.stringify
              type: 'change'
              rev: revision
              op: operation
          client.applyOperation = adapter.applyOperation
          adapter.registerCallbacks
            change: (op) -> client.applyClient(op)
          cm.setOption 'readOnly', false
        when 'ack'
          client.serverAck()
        when 'change'
          client.applyServer(msg.rev, Operation.fromJSON(msg.op))
        when 'error'
          console.log msg.msg
          console.log msg.ss

    socket.onopen = ->
      socket.send JSON.stringify
        type: 'register'   

    f = () -> Dialog.push
      title: 'connection lost'
      text: 'The connection to the server has been lost. ' +
            'All changes you make to the document now are ' +
            'only local and might get lost.'
      buttons: ['Ok']

    socket.onclose = () -> scope.$apply f
      

