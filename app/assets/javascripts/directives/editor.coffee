### @directive directives:editor ###
define ['codemirror','routes','collab/Operation','collab/CodeMirror','collab/Client','collab/Annotations'], (CodeMirror,routes,Operation,CMAdapter,Client,Annotations) -> (Dialog,$timeout,$q) -> 
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
      unless n.open        
        n.close = (a) ->
          if a is 'confirm'
            result = $q.defer()
            if n.doc.isClean()
              n.close()
              result.resolve(true)                        
            else Dialog.push
              title: 'content changed'
              text: 'the file has been modified. do you want to save your changes'
              buttons: ['Yes','No','Cancel']
              done: (answer) -> switch answer
                when 'Yes' then () ->
                  # TODO: SAVE
                  n.close()
                  result.resolve(true)
                when 'No' then () ->
                  n.close()
                  result.resolve(true)
                when 'Cancel' then () ->                
                  result.reject(false)
            return result.promise
          else
            n.open = false
            n.doc = null
        n.doc = CodeMirror.Doc('content loading...')
        n.socket = new WebSocket(routes.controllers.Application.collab(n.path).webSocketURL())
        n.open = true
        n.socket.onmessage = (e) -> 
          msg = JSON.parse(e.data)
          switch msg.type
            when 'init'
              n.doc.setValue(msg.doc)
              n.client = new Client(msg.rev)
              adapter = new CMAdapter(cm, n.doc)
              n.client.sendOperation = (revision, operation) ->
                n.socket.send JSON.stringify
                  type: 'change'
                  rev: revision
                  op: operation
              n.client.applyOperation = adapter.applyOperation
              adapter.registerCallbacks
                change: (op) -> n.client.applyClient(op)
            when 'ack'
              n.client.serverAck()
            when 'change'
              n.client.applyServer(msg.rev, Operation.fromJSON(msg.op))
            when 'error'
              console.log msg.msg
              console.log msg.ss

        n.socket.onopen = ->
          n.socket.send JSON.stringify
            type: 'register'

        n.socket.onclose = ->
          alert('connection lost!')

      cm.swapDoc(n.doc)
    