define ['concurrency/config'], (config) ->
  class Client  
    constructor: (@id, @doc) ->
      @clock = 0

    registerCallbacks: (callbacks) ->
      @callbacks = callbacks

    generateId: =>
      @clock += 1
      config.maxClients * @clock + @id

    canApplyOperation: (op) => switch op.type
      when 'insert' 
        @doc.indexOf(op.ch.previous,op.hint) >= 0 and 
        @doc.indexOf(op.ch.next,op.hint) >= 0
      when 'delete'
        @doc.indexOf(op.ch.id,op.hint) >= 0
      else undefined

    applyOperation: (op) => switch op.type
      when 'insert'
        integrate = (ch,p,n) =>
          pi = @doc.indexOf(p,op.hint)
          ni = @doc.indexOf(n,op.hint)
          if pi + 1 == ni
            @doc.insert(ch,ni)
            if @callbacks.insert
              @callbacks.insert(@doc.visible().indexOf(@doc[ni]), ch.value)
          else 
            s = @doc.subseq(pi,ni)
            l = s.filter (c) -> 
             for other in s
               return false if c.next is other.id or other.id is c.previous
             return true
            f = (l) -> for c, j in l
             return j if c.id >= ch.id
            i = f(l)
            np = l[i-1].id
            nn = l[i].id
            if np is p and nn is n
              throw new Exception "infinite loop"
            integrate(ch,np,nn)
        integrate(op.ch,op.ch.previous,op.ch.next)
        console.log @doc
      when 'hide'
        index = @doc.indexOf(op.ch.id,op.hint)
        @doc.get(index).visible = false
        if @callbacks.hide
          @callbacks.hide(@doc.visible().indexOf(@doc[index]))
      else 
        throw new Exception "invalid operation"

    generateInsert: (position, c) =>
      console.log @doc.visible()
      cp = @doc.visible()[position-1] or @doc.start
      cn = @doc.visible()[position] or @doc.end
      ch = 
        id: @generateId()
        value: c
        previous: cp.id
        next: cn.id
        visible: true
      return (
        type: 'insert'
        ch: ch
        hint: @doc.indexOf(cp.id,position)
      )

    generateHide: (position) =>
      ch = @doc.visible()[position]
      return (
        type: 'hide'
        ch: ch
        hint: @doc.indexOf(ch.id,position)
      )