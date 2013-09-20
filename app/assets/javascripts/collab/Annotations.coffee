define ['collab/Operation'], (Operation) ->  
  isPlain    = (a) -> 'number' is typeof a 
  isAnnotate = (a) -> 'object' is typeof a

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
      unless n is 0
        @length += n        
        if isAnnotate(@annotations[@annotations.length - 1]) and @annotations[@annotations.length - 1].c == o
          @annotations[@annotations.length - 1].l += str
        else
          @annotations.push
            l: n
            c: o
      return this

    @transform: (as,os) ->
      throw new Error("Both operations have to have the same base length")  if as.length isnt os.inputLength
      as = as.operations
      os = os.actions
      ai = 0
      oi = 0
      a = as[ai++]
      o = os[oi++]
      result = new Annotations()
      loop              
        if isInsert(o)
          res.plain a2.length        
          o = os[oi++]
          continue
        throw new Error("Cannot compose operations: first operation is too short.")  unless a?
        throw new Error("Cannot compose operations: first operation is too long.")  unless o?
        minl = undefined
        if isRetain(o)        
          if a > o
            minl = o
            a1 = a1 - a2
            a2 = as2[i2++]
          else if a1 is a2
            minl = o
            a1 = as1[i1++]
            a2 = as2[i2++]
          else
            minl = a
            a2 = a2 - a1
            a1 = as1[i1++]
          operation1prime.retain minl
          operation2prime.retain minl
        else if isDelete(a)        
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
        else
          throw new Error("The two operations aren't compatible")
      result