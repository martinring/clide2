define ['collaboration/Operation'], (Operation) ->  
  isPlain    = (a) -> 'number' is typeof a 
  isAnnotate = (a) -> 'object' is typeof a

  length     = (a)   -> if isPlain(a) then a   else a.l
  withLength = (a,l) -> if isPlain(a) then l else { l: l, c: a.c }

  class Annotations
    constructor: ->
      @annotations = []
      @length = 0
  
    equals = (other) ->
      return false if @length isnt other.length
      return false if @annotations.length isnt other.annotations.length
      for a, i in @annotations
        return false if a isnt other.annotations[i]
      return true
    
    plain: (n) ->
      unless n is 0
        @length += n
        if isPlain(@annotations[@annotations.length - 1])
          @annotations[@annotations.length - 1] += n
        else
          @annotations.push n
      return this

    annotate: (n,o) ->
      unless n < 0
        @length += n        
        if isAnnotate(@annotations[@annotations.length - 1]) and @annotations[@annotations.length - 1].c == o
          @annotations[@annotations.length - 1].l += str
        else
          @annotations.push
            l: n
            c: o
      return this

    add: (a) ->
      if isPlain(a) then @plain(a) else @annotate(a.l,a.c)

    @isPlain: isPlain
    @isAnnotate: isAnnotate

    compose: (other) -> other

    ###
    # An Annotation-Stream can be transformed against an Operation:
    # The cursor points to the active Annotations ENDING at the current position
    # with exception to the very first token, which is pointed to if
    # the cursor is at its start.
    ###
    transform: (op) =>
      if op.inputLength isnt @length
        throw new Error("lengths don't match")

      index     = 0
      current   = @annotations[index++]      
      remaining = length(current)

      result    = new Annotations

      for action in op.actions
        switch Operation.actionType action
          when 'insert'
            result.add withLength(current,action.length)
          when 'retain'                    
            while remaining < action
              result.add withLength(current,remaining)
              action   -= remaining
              current   = @annotations[index++]              
              remaining = length(current)
            result.add withLength(current,action)
            remaining -= action
          when 'delete'
            while remaining < (-action)
              current   = @annotations[index++]
              action   += remaining
              consumed  = 0
              remaining = length(current)
            remaining += action

      if result.length isnt op.outputLength
        throw new Error("output length doesnt match")

      return result

    @fromJSON: (annotations) ->
      result = new Annotations()
      for a in annotations
        if isPlain(a)
          result.plain(a)
        else 
          result.annotate(a.l,a.c)
      return result    