define ['collaboration/Operation'], (Operation) ->  
  isPlain    = (a) -> 'number' is typeof a 
  isAnnotate = (a) -> 'object' is typeof a

  length             = (a)   -> if isPlain(a) then a   else a.l
  withModifiedLength = (a,l) -> if l is 0 then a else if isPlain(a) then a+l else { l: a.l+l, c: a.c }

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

    compose: (other) -> other

    transform: (op) =>
      position  = 0
      current   = @annotations[position]
      remaining = length(current)
      extend    = 0

      result = new Annotations()

      next = () =>
        console.log "extending by #{extend}:"
        result.add(withModifiedLength(@annotations[position],extend))
        console.log result
        position += 1
        current = @annotations[position]
        remaining = length(current)
        extend = 0

      skip = (n) =>
        if n > remaining
          n -= remaining
          next()
          skip(n)
        else
          remaining -= n

      strip = (n) =>
        if n > remaining
          n -= remaining
          extend -= remaining          
          next()
          strip(n)
        else
          extend -= n

      for a in op.actions
        if Operation.isRetain(a)
          skip(a)
        else if Operation.isInsert(a)
          extend += a.length
        else
          strip(-a)

      result.add(withModifiedLength(@annotations[position],extend))

      return result