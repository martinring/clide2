define ['ot/TextOperation','ot/Cursor'], (TextOperation, CodeMirrorAdapter) ->
  assert = (b, msg) ->
    throw new Error(msg or "assertion error")  unless b  
  cmpPos = (a, b) ->
    return -1  if a.line < b.line
    return 1  if a.line > b.line
    return -1  if a.ch < b.ch
    return 1  if a.ch > b.ch
    0
  posEq = (a, b) ->
    cmpPos(a, b) is 0
  posLe = (a, b) ->
    cmpPos(a, b) <= 0
  codemirrorDocLength = (doc) ->
    doc.indexFromPos(
      line: doc.lastLine()
      ch: 0
    ) + doc.getLine(doc.lastLine()).length

  addStyleRule = ->
    added = {}
    styleElement = document.createElement("style")
    document.documentElement.getElementsByTagName("head")[0].appendChild styleElement
    styleSheet = styleElement.sheet
    (css) ->
      return  if added[css]
      added[css] = true
      styleSheet.insertRule css, (styleSheet.cssRules or styleSheet.rules).length
  
  class CodeMirrorAdapter
    constructor: (cm) ->
      @cm = cm
      @doc = cm.getDoc()
      @ignoreNextChange = false
      cm.on "change", @onChange
      cm.on "cursorActivity", @onCursorActivity
      cm.on "focus", @onFocus
      cm.on "blur", @onBlur

    # Removes all event listeners from the CodeMirror instance.
    detach: =>
      @cm.off "change", @onChange
      @cm.off "cursorActivity", @onCursorActivity
      @cm.off "focus", @onFocus
      @cm.off "blur", @onBlur

    # Converts a CodeMirror change object into a TextOperation and its inverse
    # and returns them as a two-element array.
    
    # Approach: Replay the changes, beginning with the most recent one, and
    # construct the operation and its inverse. We have to convert the position
    # in the pre-change coordinate system to an index. We have a method to
    # convert a position in the coordinate system after all changes to an index,
    # namely CodeMirror's `indexFromPos` method. We can use the information of
    # a single change object to convert a post-change coordinate system to a
    # pre-change coordinate system. We can now proceed inductively to get a
    # pre-change coordinate system for all changes in the linked list.
    # A disadvantage of this approach is its complexity `O(n^2)` in the length
    # of the linked list of changes.
    @operationFromCodeMirrorChange: (change, doc) ->
      last = (arr) ->
        arr[arr.length - 1]
      sumLengths = (strArr) ->
        return 0  if strArr.length is 0
        sum = 0
        i = 0

        while i < strArr.length
          sum += strArr[i].length
          i++
        sum + strArr.length - 1
      updateIndexFromPos = (indexFromPos, change) ->
        (pos) ->
          return indexFromPos(pos)  if posLe(pos, change.from)
          if posLe(change.to, pos)
            return indexFromPos(
              line: pos.line + change.text.length - 1 - (change.to.line - change.from.line)
              ch: (if (change.to.line < pos.line) then pos.ch else (if (change.text.length <= 1) then pos.ch - (change.to.ch - change.from.ch) + sumLengths(change.text) else pos.ch - change.to.ch + last(change.text).length))
            ) + sumLengths(change.removed) - sumLengths(change.text)
          return indexFromPos(change.from) + pos.ch - change.from.ch  if change.from.line is pos.line
          indexFromPos(change.from) + sumLengths(change.removed.slice(0, pos.line - change.from.line)) + 1 + pos.ch
      changes = []
      i = 0
      while change
        changes[i++] = change
        change = change.next
      docEndLength = codemirrorDocLength(doc)
      operation = new TextOperation().retain(docEndLength)
      inverse = new TextOperation().retain(docEndLength)
      indexFromPos = (pos) ->
        doc.indexFromPos pos

      i = changes.length - 1
      while i >= 0
        change = changes[i]
        indexFromPos = updateIndexFromPos(indexFromPos, change)
        fromIndex = indexFromPos(change.from)
        restLength = docEndLength - fromIndex - sumLengths(change.text)
        operation = new TextOperation().retain(fromIndex)["delete"](sumLengths(change.removed)).insert(change.text.join("\n")).retain(restLength).compose(operation)
        inverse = inverse.compose(new TextOperation().retain(fromIndex)["delete"](sumLengths(change.text)).insert(change.removed.join("\n")).retain(restLength))
        docEndLength += sumLengths(change.removed) - sumLengths(change.text)
        i--
      [operation, inverse]
    
    # Apply an operation to a CodeMirror instance.
    # holds the current index into CodeMirror's content
    @applyOperationToCodeMirror: (operation, cm) ->
      cm.operation ->
        ops = operation.ops
        index = 0
        i = 0
        l = ops.length

        while i < l
          op = ops[i]
          if TextOperation.isRetain(op)
            index += op
          else if TextOperation.isInsert(op)
            cm.replaceRange op, cm.posFromIndex(index)
            index += op.length
          else if TextOperation.isDelete(op)
            from = cm.posFromIndex(index)
            to = cm.posFromIndex(index - op)
            cm.replaceRange "", from, to
          i++


    registerCallbacks: (cb) =>
      @callbacks = cb

    onChange: (cm, change) =>
      unless @ignoreNextChange
        pair = CodeMirrorAdapter.operationFromCodeMirrorChange(change, cm)
        @trigger "change", pair[0], pair[1]
      @ignoreNextChange = false

    onCursorActivity: =>
      @trigger "cursorActivity"

    onFocus: =>
      @trigger "cursorActivity"

    onBlur: =>
      @trigger "blur"  unless @cm.somethingSelected()

    getValue: =>
      @cm.getValue()

    getCursor: =>
      cm = @cm
      cursorPos = cm.getCursor()
      position = cm.indexFromPos(cursorPos)
      selectionEnd = undefined
      if cm.somethingSelected()
        startPos = cm.getCursor(true)
        selectionEndPos = (if posEq(cursorPos, startPos) then cm.getCursor(false) else startPos)
        selectionEnd = cm.indexFromPos(selectionEndPos)
      else
        selectionEnd = position
      new Cursor(position, selectionEnd)

    CodeMirrorAdapter::setCursor = (cursor) ->
      @cm.setSelection @cm.posFromIndex(cursor.position), @cm.posFromIndex(cursor.selectionEnd)
    
    setOtherCursor: (cursor, color, clientId) =>
      cursorPos = @cm.posFromIndex(cursor.position)
      if cursor.position is cursor.selectionEnd
        cursorCoords = @cm.cursorCoords(cursorPos)
        cursorEl = document.createElement("pre")
        cursorEl.className = "other-client"
        cursorEl.style.borderLeftWidth = "2px"
        cursorEl.style.borderLeftStyle = "solid"
        cursorEl.innerHTML = "&nbsp;"
        cursorEl.style.borderLeftColor = color
        cursorEl.style.height = (cursorCoords.bottom - cursorCoords.top) * 0.9 + "px"
        cursorEl.style.marginTop = (cursorCoords.top - cursorCoords.bottom) + "px"
        cursorEl.style.zIndex = 0
        cursorEl.setAttribute "data-clientid", clientId
        @cm.addWidget cursorPos, cursorEl, false
        clear: ->
          parent = cursorEl.parentNode
          parent.removeChild cursorEl  if parent
      else
        match = /^#([0-9a-fA-F]{6})$/.exec(color)
        throw new Error("only six-digit hex colors are allowed.")  unless match
        selectionClassName = "selection-" + match[1]
        rule = "." + selectionClassName + " { background: " + color + "; }"
        addStyleRule rule
        fromPos = undefined
        toPos = undefined
        if cursor.selectionEnd > cursor.position
          fromPos = cursorPos
          toPos = @cm.posFromIndex(cursor.selectionEnd)
        else
          fromPos = @cm.posFromIndex(cursor.selectionEnd)
          toPos = cursorPos
        @cm.markText fromPos, toPos,
          className: selectionClassName


    trigger: (event,args...) =>      
      action = @callbacks and @callbacks[event]
      action.apply this, args  if action

    applyOperation: (operation) =>
      @ignoreNextChange = true
      CodeMirrorAdapter.applyOperationToCodeMirror operation, @cm

    registerUndo: (undoFn) =>
      @cm.undo = undoFn

    registerRedo: (redoFn) =>
      @cm.redo = redoFn