### @directive directives:editor ###
define ['routes','collab/Operation','collab/CodeMirror','collab/Client','collab/AnnotationStream'], (routes,Operation,CMAdapter,Client,AnnotationStream) -> (Dialog,Session,Toasts,$timeout,$q) -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],      
      lineNumbers: true
      undoDepth: 0 # disable

    scope.$watch (-> scope.$eval(iAttrs.file)), (n,o) ->       
      if n? 
        file = Session.getOpenFile(n)      
        if file
          if file.doc? # swap
            cm.swapDoc(file.doc)
            cm.focus()
          else # init
            file.doc    = CodeMirror.Doc(file.state)
            file.client = new Client(file.revision)
            adapter     = new CMAdapter(cm,file.doc)

            file.client.sendOperation = (revision, operation) ->
              Session.edit(file.info.id,revision,operation.actions)

            file.client.applyOperation = adapter.applyOperation

            adapter.registerCallbacks
              change: (op) -> file.client.applyClient(op)

            if file.pending?
              for op in file.pending
                if op is 'ack'
                  file.client.serverAck()
                if typeof op is 'array'
                  file.client.applyServer(Operation.fromJSON(msg.op))

            cm.swapDoc(file.doc)
            $timeout -> # TODO: HACK
              cm.refresh()
              cm.focus()
        else # invalid id
          Toasts.push 'danger', 'internal error: the editor has been set to invalid file id'
      else
        cm.swapDoc(CodeMirror.Doc("###"))