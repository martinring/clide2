define ->  
  isRetain = (op) ->
    typeof op is "number" and op > 0

  isInsert = (op) ->
    typeof op is "string"

  isDelete = (op) ->
    typeof op is "number" and op < 0

  isAnnotate = (op) ->
    typeof op is 'object'

  getSimpleOp = (operation) ->
    ops = operation.ops    
    switch ops.length
      when 1
        return ops[0]
      when 2
        return (if isRetain(ops[0]) then ops[1] else ((if isRetain(ops[1]) then ops[0] else null)))
      when 3
        return ops[1]  if isRetain(ops[0]) and isRetain(ops[2])
    null

  getStartIndex = (operation) ->
    if isRetain(operation.ops[0]) then operation.ops[0] else 0    

  class TextOperation
    constructor: ->
      @ops = []    
      @baseLength = 0    
      @targetLength = 0
  
    equals = (other) ->
      return false if @baseLength isnt other.baseLength
      return false if @targetLength isnt other.targetLength
      return false if @ops.length isnt other.ops.length
      for op, i in @ops
        return false if op isnt other.ops[i]      
      return true

    @isRetain: isRetain
    @isInsert: isInsert
    @isDelete: isDelete

    retain: (n) ->      
      unless n is 0
        @baseLength += n
        @targetLength += n
        if isRetain(@ops[@ops.length - 1])
          @ops[@ops.length - 1] += n
        else
          @ops.push n
      return this

    insert: (str) ->      
      unless str is ""
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
      return this

    delete: (n) ->
      n = n.length if typeof n is "string"      
      unless n is 0
        n = -n if n > 0
        @baseLength -= n
        if isDelete(@ops[@ops.length - 1])
          @ops[@ops.length - 1] += n
        else
          @ops.push n
      return this

    isNoop: ->
      @ops.length is 0 or (@ops.length is 1 and isRetain(@ops[0]))

    toJSON: ->
      @ops

    @fromJSON: (ops) ->
      result = new TextOperation()
      for op in ops
        if isRetain(op)
          result.retain op
        else if isInsert(op)
          result.insert op
        else if isDelete(op)
          result.delete op
        else
          throw new Error("unknown operation: " + JSON.stringify(op))
      return result

    compose: (operation2) ->
      operation1 = this
      if operation1.targetLength isnt operation2.baseLength
        throw new Error("The base length of the second operation has to be the target length of the first operation")
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
       
    # Transform takes two operations A and B that happened concurrently and
    # produces two operations A' and B' (in an array) such that
    # `apply(apply(S, A), B') = apply(apply(S, B), A')`. This function is the
    # heart of OT.
    @transform: (operation1, operation2) ->
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