define ->  
  # Constructor for new operations.
  TextOperation = ->
    
    # => function was called without 'new'
    return new TextOperation()  if not this or @constructor isnt TextOperation
    
    # When an operation is applied to an input string, you can think of this as
    # if an imaginary cursor runs over the entire string and skips over some
    # parts, deletes some parts and inserts characters at some positions. These
    # actions (skip/delete/insert) are stored as an array in the "ops" property.
    @ops = []
    
    # An operation's baseLength is the length of every string the operation
    # can be applied to.
    @baseLength = 0
    
    # The targetLength is the length of every string that results from applying
    # the operation on a valid input string.
    @targetLength = 0
  
  # Operation are essentially lists of ops. There are three types of ops:
  #
  # * Retain ops: Advance the cursor position by a given number of characters.
  #   Represented by positive ints.
  # * Insert ops: Insert a given string at the current cursor position.
  #   Represented by strings.
  # * Delete ops: Delete the next n characters. Represented by negative ints.
  
  # After an operation is constructed, the user of the library can specify the
  # actions of an operation (skip/insert/delete) with these three builder
  # methods. They all return the operation for convenient chaining.
  
  # Skip over a given number of characters.
  
  # The last op is a retain op => we can merge them into one op.
  
  # Create a new op.
  
  # Insert a string at the current position.
  
  # Merge insert op.
  
  # It doesn't matter when an operation is applied whether the operation
  # is delete(3), insert("something") or insert("something"), delete(3).
  # Here we enforce that in this case, the insert op always comes first.
  # This makes all operations that have the same effect when applied to
  # a document of the right length equal in respect to the `equals` method.
  
  # Delete a string at the current position.
  
  # Tests whether this operation has no effect.
  
  # Pretty printing.
  
  # map: build a new array by applying a function to every element in an old
  # array.
  
  # Converts operation into a JSON value.
  
  # Converts a plain JS object into an operation and validates it.
  
  # Apply an operation to a string, returning a new string. Throws an error if
  # there's a mismatch between the input string and the operation.
  
  # Copy skipped part of the old string.
  
  # Insert string.
  # delete op
  
  # Computes the inverse of an operation. The inverse of an operation is the
  # operation that reverts the effects of the operation, e.g. when you have an
  # operation 'insert("hello "); skip(6);' then the inverse is 'delete("hello ");
  # skip(6);'. The inverse should be used for implementing undo.
  # delete op
  
  # Compose merges two consecutive operations into one operation, that
  # preserves the changes of both. Or, in other words, for each input string S
  # and a pair of consecutive operations A and B,
  # apply(apply(S, A), B) = apply(S, compose(A, B)) must hold.
  # the combined operation
  # for fast access
  # current index into ops1 respectively ops2
  # current ops
  
  # Dispatch on the type of op1 and op2
  
  # end condition: both ops1 and ops2 have been processed
  getSimpleOp = (operation, fn) ->
    ops = operation.ops
    isRetain = TextOperation.isRetain
    switch ops.length
      when 1
        return ops[0]
      when 2
        return (if isRetain(ops[0]) then ops[1] else ((if isRetain(ops[1]) then ops[0] else null)))
      when 3
        return ops[1]  if isRetain(ops[0]) and isRetain(ops[2])
    null
  getStartIndex = (operation) ->
    return operation.ops[0]  if isRetain(operation.ops[0])
    0
  "use strict"
  TextOperation::equals = (other) ->
    return false  if @baseLength isnt other.baseLength
    return false  if @targetLength isnt other.targetLength
    return false  if @ops.length isnt other.ops.length
    i = 0

    while i < @ops.length
      return false  if @ops[i] isnt other.ops[i]
      i++
    true

  isRetain = TextOperation.isRetain = (op) ->
    typeof op is "number" and op > 0

  isInsert = TextOperation.isInsert = (op) ->
    typeof op is "string"

  isDelete = TextOperation.isDelete = (op) ->
    typeof op is "number" and op < 0

  TextOperation::retain = (n) ->
    throw new Error("retain expects an integer")  if typeof n isnt "number"
    return this  if n is 0
    @baseLength += n
    @targetLength += n
    if isRetain(@ops[@ops.length - 1])
      @ops[@ops.length - 1] += n
    else
      @ops.push n
    this

  TextOperation::insert = (str) ->
    throw new Error("insert expects a string")  if typeof str isnt "string"
    return this  if str is ""
    @targetLength += str.length
    ops = @ops
    if isInsert(ops[ops.length - 1])
      ops[ops.length - 1] += str
    else if isDelete(ops[ops.length - 1])
      if isInsert(ops[ops.length - 2])
        ops[ops.length - 2] += str
      else
        ops[ops.length] = ops[ops.length - 1]
        ops[ops.length - 2] = str
    else
      ops.push str
    this

  TextOperation::["delete"] = (n) ->
    n = n.length  if typeof n is "string"
    throw new Error("delete expects an integer or a string")  if typeof n isnt "number"
    return this  if n is 0
    n = -n  if n > 0
    @baseLength -= n
    if isDelete(@ops[@ops.length - 1])
      @ops[@ops.length - 1] += n
    else
      @ops.push n
    this

  TextOperation::isNoop = ->
    @ops.length is 0 or (@ops.length is 1 and isRetain(@ops[0]))

  TextOperation::toString = ->
    map = Array::map or (fn) ->
      arr = this
      newArr = []
      i = 0
      l = arr.length

      while i < l
        newArr[i] = fn(arr[i])
        i++
      newArr

    map.call(@ops, (op) ->
      if isRetain(op)
        "retain " + op
      else if isInsert(op)
        "insert '" + op + "'"
      else
        "delete " + (-op)
    ).join ", "

  TextOperation::toJSON = ->
    @ops

  TextOperation.fromJSON = (ops) ->
    o = new TextOperation()
    i = 0
    l = ops.length

    while i < l
      op = ops[i]
      if isRetain(op)
        o.retain op
      else if isInsert(op)
        o.insert op
      else if isDelete(op)
        o["delete"] op
      else
        throw new Error("unknown operation: " + JSON.stringify(op))
      i++
    o

  TextOperation::apply = (str) ->
    operation = this
    throw new Error("The operation's base length must be equal to the string's length.")  if str.length isnt operation.baseLength
    newStr = []
    j = 0
    strIndex = 0
    ops = @ops
    i = 0
    l = ops.length

    while i < l
      op = ops[i]
      if isRetain(op)
        throw new Error("Operation can't retain more characters than are left in the string.")  if strIndex + op > str.length
        newStr[j++] = str.slice(strIndex, strIndex + op)
        strIndex += op
      else if isInsert(op)
        newStr[j++] = op
      else
        strIndex -= op
      i++
    throw new Error("The operation didn't operate on the whole string.")  if strIndex isnt str.length
    newStr.join ""

  TextOperation::invert = (str) ->
    strIndex = 0
    inverse = new TextOperation()
    ops = @ops
    i = 0
    l = ops.length

    while i < l
      op = ops[i]
      if isRetain(op)
        inverse.retain op
        strIndex += op
      else if isInsert(op)
        inverse["delete"] op.length
      else
        inverse.insert str.slice(strIndex, strIndex - op)
        strIndex -= op
      i++
    inverse

  TextOperation::compose = (operation2) ->
    operation1 = this
    throw new Error("The base length of the second operation has to be the target length of the first operation")  if operation1.targetLength isnt operation2.baseLength
    operation = new TextOperation()
    ops1 = operation1.ops
    ops2 = operation2.ops
    i1 = 0
    i2 = 0
    op1 = ops1[i1++]
    op2 = ops2[i2++]
    loop
      break  if typeof op1 is "undefined" and typeof op2 is "undefined"
      if isDelete(op1)
        operation["delete"] op1
        op1 = ops1[i1++]
        continue
      if isInsert(op2)
        operation.insert op2
        op2 = ops2[i2++]
        continue
      throw new Error("Cannot compose operations: first operation is too short.")  if typeof op1 is "undefined"
      throw new Error("Cannot compose operations: first operation is too long.")  if typeof op2 is "undefined"
      if isRetain(op1) and isRetain(op2)
        if op1 > op2
          operation.retain op2
          op1 = op1 - op2
          op2 = ops2[i2++]
        else if op1 is op2
          operation.retain op1
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          operation.retain op1
          op2 = op2 - op1
          op1 = ops1[i1++]
      else if isInsert(op1) and isDelete(op2)
        if op1.length > -op2
          op1 = op1.slice(-op2)
          op2 = ops2[i2++]
        else if op1.length is -op2
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          op2 = op2 + op1.length
          op1 = ops1[i1++]
      else if isInsert(op1) and isRetain(op2)
        if op1.length > op2
          operation.insert op1.slice(0, op2)
          op1 = op1.slice(op2)
          op2 = ops2[i2++]
        else if op1.length is op2
          operation.insert op1
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          operation.insert op1
          op2 = op2 - op1.length
          op1 = ops1[i1++]
      else if isRetain(op1) and isDelete(op2)
        if op1 > -op2
          operation["delete"] op2
          op1 = op1 + op2
          op2 = ops2[i2++]
        else if op1 is -op2
          operation["delete"] op2
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          operation["delete"] op1
          op2 = op2 + op1
          op1 = ops1[i1++]
      else
        throw new Error("This shouldn't happen: op1: " + JSON.stringify(op1) + ", op2: " + JSON.stringify(op2))
    operation

  
  # When you use ctrl-z to undo your latest changes, you expect the program not
  # to undo every single keystroke but to undo your last sentence you wrote at
  # a stretch or the deletion you did by holding the backspace key down. This
  # This can be implemented by composing operations on the undo stack. This
  # method can help decide whether two operations should be composed. It
  # returns true if the operations are consecutive insert operations or both
  # operations delete text at the same position. You may want to include other
  # factors like the time since the last change in your decision.
  TextOperation::shouldBeComposedWith = (other) ->
    return true  if @isNoop() or other.isNoop()
    startA = getStartIndex(this)
    startB = getStartIndex(other)
    simpleA = getSimpleOp(this)
    simpleB = getSimpleOp(other)
    return false  if not simpleA or not simpleB
    return startA + simpleA.length is startB  if isInsert(simpleA) and isInsert(simpleB)
    
    # there are two possibilities to delete: with backspace and with the
    # delete key.
    return (startB - simpleB is startA) or startA is startB  if isDelete(simpleA) and isDelete(simpleB)
    false

  
  # Decides whether two operations should be composed with each other
  # if they were inverted, that is
  # `shouldBeComposedWith(a, b) = shouldBeComposedWithInverted(b^{-1}, a^{-1})`.
  TextOperation::shouldBeComposedWithInverted = (other) ->
    return true  if @isNoop() or other.isNoop()
    startA = getStartIndex(this)
    startB = getStartIndex(other)
    simpleA = getSimpleOp(this)
    simpleB = getSimpleOp(other)
    return false  if not simpleA or not simpleB
    return startA + simpleA.length is startB or startA is startB  if isInsert(simpleA) and isInsert(simpleB)
    return startB - simpleB is startA  if isDelete(simpleA) and isDelete(simpleB)
    false

  
  # Transform takes two operations A and B that happened concurrently and
  # produces two operations A' and B' (in an array) such that
  # `apply(apply(S, A), B') = apply(apply(S, B), A')`. This function is the
  # heart of OT.
  TextOperation.transform = (operation1, operation2) ->
    throw new Error("Both operations have to have the same base length")  if operation1.baseLength isnt operation2.baseLength
    operation1prime = new TextOperation()
    operation2prime = new TextOperation()
    ops1 = operation1.ops
    ops2 = operation2.ops
    i1 = 0
    i2 = 0
    op1 = ops1[i1++]
    op2 = ops2[i2++]
    loop
      
      # At every iteration of the loop, the imaginary cursor that both
      # operation1 and operation2 have that operates on the input string must
      # have the same position in the input string.
      
      # end condition: both ops1 and ops2 have been processed
      break  if typeof op1 is "undefined" and typeof op2 is "undefined"
      
      # next two cases: one or both ops are insert ops
      # => insert the string in the corresponding prime operation, skip it in
      # the other one. If both op1 and op2 are insert ops, prefer op1.
      if isInsert(op1)
        operation1prime.insert op1
        operation2prime.retain op1.length
        op1 = ops1[i1++]
        continue
      if isInsert(op2)
        operation1prime.retain op2.length
        operation2prime.insert op2
        op2 = ops2[i2++]
        continue
      throw new Error("Cannot compose operations: first operation is too short.")  if typeof op1 is "undefined"
      throw new Error("Cannot compose operations: first operation is too long.")  if typeof op2 is "undefined"
      minl = undefined
      if isRetain(op1) and isRetain(op2)
        
        # Simple case: retain/retain
        if op1 > op2
          minl = op2
          op1 = op1 - op2
          op2 = ops2[i2++]
        else if op1 is op2
          minl = op2
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          minl = op1
          op2 = op2 - op1
          op1 = ops1[i1++]
        operation1prime.retain minl
        operation2prime.retain minl
      else if isDelete(op1) and isDelete(op2)
        
        # Both operations delete the same string at the same position. We don't
        # need to produce any operations, we just skip over the delete ops and
        # handle the case that one operation deletes more than the other.
        if -op1 > -op2
          op1 = op1 - op2
          op2 = ops2[i2++]
        else if op1 is op2
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          op2 = op2 - op1
          op1 = ops1[i1++]
      
      # next two cases: delete/retain and retain/delete
      else if isDelete(op1) and isRetain(op2)
        if -op1 > op2
          minl = op2
          op1 = op1 + op2
          op2 = ops2[i2++]
        else if -op1 is op2
          minl = op2
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          minl = -op1
          op2 = op2 + op1
          op1 = ops1[i1++]
        operation1prime["delete"] minl
      else if isRetain(op1) and isDelete(op2)
        if op1 > -op2
          minl = -op2
          op1 = op1 + op2
          op2 = ops2[i2++]
        else if op1 is -op2
          minl = op1
          op1 = ops1[i1++]
          op2 = ops2[i2++]
        else
          minl = op1
          op2 = op2 + op1
          op1 = ops1[i1++]
        operation2prime["delete"] minl
      else
        throw new Error("The two operations aren't compatible")
    [operation1prime, operation2prime]

  TextOperation