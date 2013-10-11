define ['collaboration/Operation','collaboration/Annotations'], (Operation,Annotations) ->
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
                                .annotate(0,{'c':'cursor'})
                                .plain(length - head)
      else
        return new Annotations().plain(head)
                                .annotate(0,{'c':'cursor'})
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

    annotate: (c,user,from,to) =>
      if c.e?        
        if cm = @doc.getEditor()
          widget = document.createElement("div")
          widget.setAttribute('class','outputWidget error')
          widget.innerText = c.e
          widget = cm.addLineWidget from.line, widget
          @annotations[user.id].push widget
      if c.c?
        if to?
          marker = @doc.markText from, to,
            className: c.c
          @annotations[user.id].push marker
        else
          widget = document.createElement("span")
          widget.setAttribute('class', c.c)
          bookmark = @doc.setBookmark from,
            widget: widget
            insertLeft: true
          @annotations[user.id].push bookmark        

    applyAnnotation: (annotation, user) =>
      cm       = @doc.getEditor()

      work = =>        
        if @annotations[user.id]?          
          console.log 'clearing markers'
          for marker in @annotations[user.id]
            console.log 'clearing marker'
            marker.clear()

        @annotations[user.id] = []

        index = 0 # TODO: Iterate Line/Column based with cm.eachLine
        for a in annotation.annotations
          if Annotations.isPlain(a)
            index += a
          else
            from = @doc.posFromIndex(index)            
            if a.l > 0
              index += a.l
              to = @doc.posFromIndex(index)
              @annotate(a.c,user,from,to)
            else
               @annotate(a.c,user,from)        

      if cm? then cm.operation => work()
      else work()