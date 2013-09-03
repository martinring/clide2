### @directive directives:editor ###
define ['codemirror','routes','collab/Operation','collab/CodeMirror','collab/Client','collab/AnnotationStream'], (CodeMirror,routes,Operation,CMAdapter,Client,AnnotationStream) -> (Dialog,Session,$timeout,$q) -> 
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
            Session.send
              type: 'leave'
              path: n.path
            Session.ignore n.path          
        
        n.open = true

        Session.listen n.path, (msg) ->           
          switch msg.type
            when 'init'           
              n.doc = CodeMirror.Doc(msg.text)              
              cm.swapDoc(n.doc)
              cm.setOption 'mode', 
                name: 'remote'
                annotations: n.as or []            
              n.client = new Client(msg.rev)
              adapter = new CMAdapter(cm, n.doc)
              n.client.sendOperation = (revision, operation) ->
                Session.send
                  path: n.path
                  type: 'change'
                  rev: revision
                  op: operation.actions
              n.client.applyOperation = adapter.applyOperation            
              adapter.registerCallbacks
                change: (op) -> n.client.applyClient(op)
              console.log 'initialized'
            when 'ack'
              n.client.serverAck()
            when 'edit'
              n.client.applyServer(Operation.fromJSON(msg.op))
            when 'ann'
              n.as = msg.as
              n.doc.getEditor()?.setOption 'mode',
                name: 'remote'
                annotations: n.as              
            when 'error'
              console.log msg.msg
              console.log msg.ss          
        Session.send
          type: 'register'
          path: n.path
      else
        cm.swapDoc(n.doc)
        cm.setOption 'mode', n.mode