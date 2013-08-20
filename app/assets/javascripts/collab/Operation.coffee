define ->  
  actionType = (action) ->
    switch typeof action
      when 'number'
        if action > 0
          return "retain"
        if action < 0
          return "delete"
      when "string"
        return "insert"
    return undefined

  isRetain = (action) ->
    typeof action is "number" and action > 0

  isInsert = (action) ->
    typeof action is "string"

  isDelete = (action) ->
    typeof action is "number" and action < 0  

  getSimpleOp = (operation) ->
    actions = operation.actions    
    switch actions.length
      when 1
        return actions[0]
      when 2
        if isRetain(actions[0]) 
          return actions[1] 
        if isRetain(actions[1]) 
          return actions[0]
      when 3
        if isRetain(actions[0]) and isRetain(actions[2])
          return actions[1]
    null

  getStartIndex = (operation) ->
    if isRetain(operation.actions[0]) then operation.actions[0] else 0    

  class Operation
    constructor: ->
      @actions = []    
      @inputLength = 0    
      @outputLength = 0
  
    equals = (other) ->
      return false if @inputLength isnt other.inputLength
      return false if @outputLength isnt other.outputLength
      return false if @actions.length isnt other.actions.length
      for a, i in @actions
        return false if a isnt other.actions[i]      
      return true

    @isRetain: isRetain
    @isInsert: isInsert
    @isDelete: isDelete
    @actionType: actionType

    retain: (n) ->      
      unless n is 0
        @inputLength += n
        @outputLength += n
        if isRetain(@actions[@actions.length - 1])
          @actions[@actions.length - 1] += n
        else
          @actions.push n
      return this

    insert: (str) ->      
      unless str is ""
        @outputLength += str.length
        actions = @actions
        if isInsert(actions[actions.length - 1])
          actions[actions.length - 1] += str
        else if isDelete(actions[actions.length - 1])
          if isInsert(actions[actions.length - 2])
            actions[actions.length - 2] += str
          else
            actions[actions.length] = actions[actions.length - 1]
            actions[actions.length - 2] = str
        else
          actions.push str
      return this

    delete: (n) ->
      n = n.length if typeof n is "string"      
      unless n is 0
        n = -n if n > 0
        @inputLength -= n
        if isDelete(@actions[@actions.length - 1])
          @actions[@actions.length - 1] += n
        else
          @actions.push n
      return this

    isNoop: ->
      @actions.length is 0 or (@actions.length is 1 and isRetain(@actions[0]))

    toJSON: ->
      @actions

    @fromJSON: (actions) ->
      result = new Operation()
      for a in actions
        switch a 
          when 'retain' then result.retain a
          when 'insert' then result.insert a
          when 'delete' then result.delete a
          else throw new Error("unknown operation: "+JSON.stringify(op))
      return result

    compose: (operation2) ->
      operation1 = this
      if operation1.outputLength isnt operation2.inputLength
        throw new Error("The base length of the second operation has to be the target length of the first operation")
      operation = new Operation()
      as1 = operation1.actions
      as2 = operation2.actions
      i1 = 0
      i2 = 0
      a1 = as1[i1++]
      a2 = as2[i2++]
      loop
        break if typeof a1 is "undefined" and typeof a2 is "undefined"
        if isDelete(a1)
          operation["delete"] a1
          a1 = as1[i1++]
          continue
        if isInsert(a2)
          operation.insert a2
          a2 = as2[i2++]
          continue
        throw new Error("Cannot compose operations: first operation is too short.")  if typeof a1 is "undefined"
        throw new Error("Cannot compose operations: first operation is too long.")  if typeof a2 is "undefined"
        if isRetain(a1) and isRetain(a2)
          if a1 > a2
            operation.retain a2
            a1 = a1 - a2
            a2 = as2[i2++]
          else if a1 is a2
            operation.retain a1
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            operation.retain a1
            a2 = a2 - a1
            a1 = as1[i1++]
        else if isInsert(a1) and isDelete(a2)
          if a1.length > -a2
            a1 = a1.slice(-a2)
            a2 = as2[i2++]
          else if a1.length is -a2
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            a2 = a2 + a1.length
            a1 = as1[i1++]
        else if isInsert(a1) and isRetain(a2)
          if a1.length > a2
            operation.insert a1.slice(0, a2)
            a1 = a1.slice(a2)
            a2 = as2[i2++]
          else if a1.length is a2
            operation.insert a1
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            operation.insert a1
            a2 = a2 - a1.length
            a1 = as1[i1++]
        else if isRetain(a1) and isDelete(a2)
          if a1 > -a2
            operation["delete"] a2
            a1 = a1 + a2
            a2 = as2[i2++]
          else if a1 is -a2
            operation["delete"] a2
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            operation["delete"] a1
            a2 = a2 + a1
            a1 = as1[i1++]
        else
          throw new Error("This shouldn't happen: a1: " + JSON.stringify(a1) + ", a2: " + JSON.stringify(a2))
      operation
       
    # Transform takes two operations A and B that happened concurrently and
    # produces two operations A' and B' (in an array) such that
    # `apply(apply(S, A), B') = apply(apply(S, B), A')`. This function is the
    # heart of OT.
    @transform: (operation1, operation2) ->
      throw new Error("Both operations have to have the same base length")  if operation1.inputLength isnt operation2.inputLength
      operation1prime = new Operation()
      operation2prime = new Operation()
      as1 = operation1.actions
      as2 = operation2.actions
      i1 = 0
      i2 = 0
      a1 = as1[i1++]
      a2 = as2[i2++]
      loop        
        # At every iteration of the loop, the imaginary cursor that both
        # operation1 and operation2 have that operates on the input string must
        # have the same position in the input string.
        
        # end condition: both as1 and as2 have been processed
        break  if typeof a1 is "undefined" and typeof a2 is "undefined"
        
        # next two cases: one or both actions are insert actions
        # => insert the string in the corresponding prime operation, skip it in
        # the other one. If both a1 and a2 are insert actions, prefer a1.
        if isInsert(a1)
          operation1prime.insert a1
          operation2prime.retain a1.length
          a1 = as1[i1++]
          continue
        if isInsert(a2)
          operation1prime.retain a2.length
          operation2prime.insert a2
          a2 = as2[i2++]
          continue
        throw new Error("Cannot compose operations: first operation is too short.")  if typeof a1 is "undefined"
        throw new Error("Cannot compose operations: first operation is too long.")  if typeof a2 is "undefined"
        minl = undefined
        if isRetain(a1) and isRetain(a2)
          
          # Simple case: retain/retain
          if a1 > a2
            minl = a2
            a1 = a1 - a2
            a2 = as2[i2++]
          else if a1 is a2
            minl = a2
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            minl = a1
            a2 = a2 - a1
            a1 = as1[i1++]
          operation1prime.retain minl
          operation2prime.retain minl
        else if isDelete(a1) and isDelete(a2)
          
          # Both operations delete the same string at the same position. We don't
          # need to produce any operations, we just skip over the delete actions and
          # handle the case that one operation deletes more than the other.
          if -a1 > -a2
            a1 = a1 - a2
            a2 = as2[i2++]
          else if a1 is a2
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            a2 = a2 - a1
            a1 = as1[i1++]
        
        # next two cases: delete/retain and retain/delete
        else if isDelete(a1) and isRetain(a2)
          if -a1 > a2
            minl = a2
            a1 = a1 + a2
            a2 = as2[i2++]
          else if -a1 is a2
            minl = a2
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            minl = -a1
            a2 = a2 + a1
            a1 = as1[i1++]
          operation1prime["delete"] minl
        else if isRetain(a1) and isDelete(a2)
          if a1 > -a2
            minl = -a2
            a1 = a1 + a2
            a2 = as2[i2++]
          else if a1 is -a2
            minl = a1
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            minl = a1
            a2 = a2 + a1
            a1 = as1[i1++]
          operation2prime["delete"] minl
        else
          throw new Error("The two operations aren't compatible")
      [operation1prime, operation2prime]