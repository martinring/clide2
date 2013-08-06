define ['concurrency/config'], (config) ->
  class Document
    constructor: ->
      @start = 
        id: 0
        next: config.maxClients
      @end =
        id: config.maxClients
        previous: 0
      @sequence = [@start,@end]

    length: =>
      @sequence.length

    get: (pos) =>
      @sequence[pos]    

    indexOf: (id,hint) =>
      h = hint or 0
      for i in [h...@sequence.length]
        if @sequence[i]?.id is id then return i
      return -1

    insert: (ch,pos) =>
      @sequence[pos...pos] = ch

    subseq: (from,to) =>
      f = from + 1
      @sequence[f...to]

    visible: =>
      @sequence.filter (x) -> x.visible

    value: =>
      @visible().map (x) -> x.value

    toString: =>
      @value().join