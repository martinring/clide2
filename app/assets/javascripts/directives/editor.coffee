### @directive directives:editor ###
define ['codemirror','routes','collab/Operation','collab/CodeMirror','collab/Client','collab/Annotations'], (CodeMirror,routes,Operation,CMAdapter,Client,Annotations) -> (Dialog,Session,$timeout,$q) -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],      
      lineNumbers: true      
      undoDepth: 0 # disable      

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
            Session.ignore n.path            
                
        Session.listen n.path, (msg) ->           
          switch msg.type
            when 'init'            
              n.doc = CodeMirror.Doc(msg.text)
              cm.swapDoc(n.doc)
              n.client = new Client(msg.rev)
              adapter = new CMAdapter(cm, n.doc)
              n.client.sendOperation = (revision, operation) ->
                Session.send
                  path: n.path
                  type: 'change'
                  rev: revision
                  op: operation
              n.client.applyOperation = adapter.applyOperation            
              adapter.registerCallbacks
                change: (op) -> n.client.applyClient(op)
              console.log 'initialized'
            when 'ack'
              n.client.serverAck()
            when 'change'
              n.client.applyServer(msg.rev, Operation.fromJSON(msg.op))
            when 'error'
              console.log msg.msg
              console.log msg.ss

        Session.send
          type: 'register'
          path: n.path