define ['ot/TextOperation'], (TextOperation) -> 
  # A cursor has a `position` and a `selectionEnd`. Both are zero-based indexes
  # into the document. When nothing is selected, `selectionEnd` is equal to
  # `position`. When there is a selection, `position` is always the side of the
  # selection that would move if you pressed an arrow key.
  Cursor = (position, selectionEnd) ->
    @position = position
    @selectionEnd = selectionEnd
  
  Cursor.fromJSON = (obj) ->
    new Cursor(obj.position, obj.selectionEnd)

  Cursor::equals = (other) ->
    @position is other.position and @selectionEnd is other.selectionEnd

  
  # Return the more current cursor information.
  Cursor::compose = (other) ->
    other
  
  # Update the cursor with respect to an operation.
  Cursor::transform = (other) ->
    transformIndex = (index) ->
      newIndex = index
      ops = other.ops
      i = 0
      l = other.ops.length

      while i < l
        if TextOperation.isRetain(ops[i])
          index -= ops[i]
        else if TextOperation.isInsert(ops[i])
          newIndex += ops[i].length
        else
          newIndex -= Math.min(index, -ops[i])
          index += ops[i]
        break  if index < 0
        i++
      newIndex
    newPosition = transformIndex(@position)
    return new Cursor(newPosition, newPosition)  if @position is @selectionEnd
    new Cursor(newPosition, transformIndex(@selectionEnd))

  Cursor