define ['concurrency/TextOperation'], (TextOperation) ->
  assert = (b, msg) ->
    throw new Error(msg or "assertion error")  unless b  

  class CodeMirrorAdapter
    constructor: (@cm) ->      
      cm.on "beforeChange", @onChange
      cm.on "cursorActivity", @onCursorActivity
      cm.on "focus", @onFocus
      cm.on "blur", @onBlur

    # Removes all event listeners from the CodeMirror instance.
    detach: =>
      @cm.off "beforeChange", @onChange
      @cm.off "cursorActivity", @onCursorActivity
      @cm.off "focus", @onFocus
      @cm.off "blur", @onBlur

    # Converts a CodeMirror change object into a TextOperation
    @operationFromCodeMirrorChange: (change, doc) ->      
      from = doc.indexFromPos(change.from)
      to   = doc.indexFromPos(change.to)
      length = to - from      
      new TextOperation().retain(from)
                         .delete(length)
                         .insert(change.text.join('\n') )
                         .retain(doc.getValue().length - to)      
      
    # Apply an operation to a CodeMirror instance.
    # holds the current index into CodeMirror's content
    @applyOperationToCodeMirror: (operation, cm) -> cm.operation ->      
      index = 0
      markers = { }
      for op in operation.ops
        if TextOperation.isRetain(op)
          index += op
        else if TextOperation.isInsert(op)
          cm.replaceRange op, cm.posFromIndex(index)
          index += op.length
        else if TextOperation.isDelete(op)
          from = cm.posFromIndex(index)
          to = cm.posFromIndex(index - op)
          cm.replaceRange "", from, to
        else if TextOperation.isAnnotate(op)
          for mark, i in op.starting
            pendingMarkers[mark] = 
              startIndex: index
              attributes: op.attributes[i]
          for mark in op.ending
            marker = markers[mark]
            cm.markText cm.posFromIndex(marker.startIndex), cm.posFromIndex(index), marker.attributes

    registerCallbacks: (cb) =>
      @callbacks = cb

    onChange: (cm, change) =>
      unless @silent        
        @trigger "change", CodeMirrorAdapter.operationFromCodeMirrorChange(change, cm)

    onCursorActivity: => @trigger "cursorActivity"
    onFocus: => @trigger "cursorActivity"
    onBlur: => @trigger "blur" unless @cm.somethingSelected()

    getValue: => @cm.getValue()

    trigger: (event,args...) =>      
      action = @callbacks and @callbacks[event]
      action.apply this, args  if action

    applyOperation: (operation) =>
      @silent = true
      CodeMirrorAdapter.applyOperationToCodeMirror operation, @cm
      @silent = false