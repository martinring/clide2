define ['collaboration/Operation'], (Operation) ->  
  isPlain    = (a) -> 'number' is typeof a 
  isAnnotate = (a) -> 'object' is typeof a

  length     = (a)   -> if isPlain(a) then return a else return a.l
  withLength = (a,l) -> if isPlain(a) then return l else return { l: l, c: a.c }

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
          @annotations[@annotations.length - 1].l += n
        else
          @annotations.push
            l: n
            c: o
      return this

    add: (a) ->
      if isPlain(a) then @plain(a) else @annotate(a.l,a.c)

    @isPlain: isPlain
    @isAnnotate: isAnnotate
    @len: length
    @withLength: withLength

    compose: (other) -> other

    transform: (op) => 
      try
        Annotations.transform(@,op)
      catch error
        console.error "annotation could not be transformed: #{error}"
        console.warn  "falling back to plain annotation"        
        new Annotations().plain(op.outputLength)

    @transform: (annotations, operation) ->
      throw new Error("Both operations have to have the same base length")  if annotations.length isnt operation.inputLength
      result = new Annotations()      
      as = annotations.annotations
      os = operation.actions
      ai = oi = 0      
      a = as[ai++]
      o = os[oi++]
      loop        
        break  if typeof a is "undefined" and typeof o is "undefined"        
        if Operation.isInsert(o)
          if a?
            result.add(withLength(a, o.length))
          else
            result.plain(o.length)
          o = os[oi++]
          continue
        throw new Error("Cannot compose: annotations are too short.")  if typeof a is "undefined"
        throw new Error("Cannot compose: annotations are too long.")   if typeof o is "undefined"        
        if Operation.isRetain(o)
          if length(a) > o            
            result.add(withLength(a, o))
            a = withLength(a, length(a)-o)            
            o = os[oi++]
          else if length(a) is o            
            result.add(withLength(a, o))
            a = as[ai++]
            o = os[oi++]
          else
            result.add(withLength(a, length(a)))
            o = o - length(a)
            a = as[ai++]          
        else if Operation.isDelete(o)
          if length(a) > -o
            a = withLength(a, length(a) + o)
            o = os[oi++]
          else if length(a) is -o
            a = as[ai++]
            o = os[oi++]
          else
            o = o + length(a)
            a = as[ai++]          
        else
          throw new Error("The operation isn't compatible with the annotation")
      result

    @fromJSON: (annotations) ->
      result = new Annotations()
      for a in annotations
        if isPlain(a)
          result.plain(a)
        else 
          result.annotate(a.l,a.c)
      return result    