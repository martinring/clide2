define ['collab/Operation'], (Operation) ->
  class CodeMirrorAdapter
    constructor: (@cm,@doc) ->      
      @doc.on "beforeChange", @onChange

    # Removes all event listeners from the CodeMirror instance.
    detach: =>
      @doc.off "beforeChange", @onChange

    # Converts a CodeMirror change object into a Operation
    @operationFromCodeMirrorChange: (change, doc) ->      
      from = doc.indexFromPos(change.from)
      to   = doc.indexFromPos(change.to)
      length = to - from      
      new Operation().retain(from)
                         .delete(length)
                         .insert(change.text.join('\n') )
                         .retain(doc.getValue().length-to) # could be cached
      
    # Apply an operation to a CodeMirror instance.
    @applyOperationToCodeMirror: (operation, cm, doc) -> cm.operation ->
      index = 0
      for a in operation.actions
        switch Operation.actionType(a)
          when 'retain'        
            index += a
          when 'insert'
            doc.replaceRange a, doc.posFromIndex(index)
            index += a.length
          when 'delete'
            from = doc.posFromIndex(index)
            to = doc.posFromIndex(index - a)
            doc.replaceRange "", from, to

    registerCallbacks: (cb) =>
      @callbacks = cb

    onChange: (doc, change) =>
      unless @silent        
        @trigger "change", CodeMirrorAdapter.operationFromCodeMirrorChange(change, doc)

    getValue: => @doc.getValue()

    trigger: (event,args...) =>
      action = @callbacks and @callbacks[event]
      action.apply this, args  if action

    applyOperation: (operation) =>
      @silent = true
      CodeMirrorAdapter.applyOperationToCodeMirror operation, @cm, @doc
      @silent = false