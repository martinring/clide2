define ['collaboration/Operation','collaboration/Annotations'], (Operation,Annotations) ->
  skipOne = (state) ->
    if state.remaining.length > 0
      switch typeof state.remaining[0]
        when 'number'
          if state.remaining[0] > 0
            state.remaining[0]--
          else
            state.remaining.splice(0,1)                      

  CodeMirror.defineMode 'remote', (cmconf,config) ->
    startState: ->       
      remaining: config.annotations?.slice() or []      
    blankLine: skipOne
    token: (stream,state) ->      
      if state.remaining.length > 0
        current = state.remaining[0]
        switch typeof current
          when 'number'
            while current > 0 and stream.next()?
              current -= 1
            if current > 0
              state.remaining[0] = current
            else
              state.remaining.splice(0,1)
            skipOne(state) if (stream.eol())
            return null
          when 'object'
            length = current.l
            while length > 0 and stream.next()?
              length -= 1
            if length > 0
              state.remaining[0] =
                l: length
                c: current.c
            else
              state.remaining.splice(0,1)
            skipOne(state) if (stream.eol())
            return current.c['class']
          else
            console.error 'unknown annotation type'
      else
        stream.skipToEnd()
        return null

  class CodeMirrorAdapter
    constructor: (@doc) ->
      @doc.on "beforeChange", @onChange
      @doc.on "beforeSelectionChange", @onSelectionChange
      @annotations = {}

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
    @applyOperationToCodeMirror: (operation, doc) ->
      index = 0 # TODO: Iterate Line/Column based
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

    @annotationFromCodeMirrorSelection: (doc,selection) ->
      anchor = doc.indexFromPos(selection.anchor)
      head   = doc.indexFromPos(selection.head)

      length = doc.getValue().length # TODO: see above
                  
      if anchor is head
        return new Annotations().plain(anchor)
                                .annotate(0,{'c':'cursor'})
                                .plain(length - anchor)
      else if anchor < head
        return new Annotations().plain(anchor)                                
                                .annotate(head - anchor,{'c':'selection'})
                                .plain(length - head)
      else
        return new Annotations().plain(head)
                                .annotate(anchor - head,{'c':'selection'})                                
                                .plain(length - anchor)

    registerCallbacks: (cb) =>
      @callbacks = cb

    onChange: (doc, change) =>
      unless @silent      
        @trigger "change", CodeMirrorAdapter.operationFromCodeMirrorChange(change, doc)

    onSelectionChange: (doc, change) =>
      unless @silent      
        @trigger "annotate", CodeMirrorAdapter.annotationFromCodeMirrorSelection(doc, change)

    getValue: => @doc.getValue()

    trigger: (event,args...) =>
      action = @callbacks and @callbacks[event]
      action.apply this, args  if action

    applyOperation: (operation) =>
      @silent = true
      cm = @doc.getEditor()
      if cm? then cm.operation =>
        CodeMirrorAdapter.applyOperationToCodeMirror operation, @doc
      else
        CodeMirrorAdapter.applyOperationToCodeMirror operation, @doc  
      @silent = false  

    applyAnnotation: (annotation, user) =>
      cm = @doc.getEditor()
      existing = @annotations[user.id]
      if existing? then for marker in existing
        marker.clear()
      if cm? then cm.operation =>
        @annotations[user.id] = []
        index = 0 # TODO: Iterate Line/Column based
        for a in annotation.annotations
          if Annotations.isPlain(a)
            index += a
          else
            from = @doc.posFromIndex(index)            
            if a.l > 0
              index += a.l
              to     = @doc.posFromIndex(index)
              @annotations[user.id].push @doc.markText from, to,
                className: a.c.c + " " + user.color
                inclusiveLeft: false
                inclusiveRight: true
            else
              widget = document.createElement("span")              
              widget.setAttribute('class', a.c.c + " " + user.color)
              @annotations[user.id].push @doc.setBookmark from,
                widget: widget
                insertLeft: true