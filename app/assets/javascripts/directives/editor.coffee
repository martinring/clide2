# usage:
# <editor file="{path}"/>
define ['codemirror','routes','ot/TextOperation','ot/CodeMirrorAdapter','ot/Client'], (CodeMirror,routes,TextOperation,CodeMirrorAdapter,Client) -> () -> 
  restrict: 'E'
  transclude: true
  controller: ($scope, $element) ->
    null
  template: '<textarea ng-transclude></textarea>'
  replace: true
  link: (scope, iElem, iAttrs, controller) ->    
    cm = CodeMirror.fromTextArea iElem[0],
      lineNumbers: true    
    socket = new WebSocket(routes.controllers.Application.collab().webSocketURL())
    client = null
    socket.onmessage = (e) -> 
      msg = JSON.parse(e.data)
      switch msg.type
        when 'init'
          console.log 'initialized', msg.rev, msg.doc
          cm.setValue(msg.doc)          
          client = new Client(msg.rev)
          adapter = new CodeMirrorAdapter(cm)
          client.sendOperation = (revision, operation) ->
            socket.send JSON.stringify
              rev: revision
              op: operation
          client.applyOperation = adapter.applyOperation
          adapter.registerCallbacks            
            change: (f,unf) -> client.applyClient(f)
        when 'ack'
          client.serverAck()
        when 'change'
          client.applyServer(TextOperation.fromJSON(msg.op))
        when 'error'
          console.log msg.msg
          console.log msg.ss