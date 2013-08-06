#define (clientId) ->
#  # 2^53 is the maximum integer that can be exactly represented in
#  # js without rounding:
#  # > 9007199254740992 + 1
#  # = 9007199254740992
#  maxInt = 9007199254740992 
#
#  # The maximum number of clients concurrently editing a document
#  maxClients = 16
#
#  if clientId >= (maxClients - 1)
#    throw new Exception 'invalid client id'
#
#  # a local clock to creaty unique ids for characters
#  clock = 0
#
#  # yields the next unique id and increases the local clock
#  nextId = ->
#    base + maxClients * (clock++)
#
#  # A WChar is a four tuple:
#  ## - value: the actual character represented by the WChar
#  # - next: the id of the following WChar at time of insertion
#  # - previous: the id of the previous WChar at time of insertion
#  # - id: the unique id of this WChar
#  class WChar
#    constructor: (@value,@next,@previous,id) ->
#      @id = id or nextId()
#  
#  class WString   
#    constructor: ->
#      @start =
#        id:   0
#        next: maxClients
#      @end =
#        id:       maxClients
#        previous: 0
#      @seq = [start,end]          
#
#    length: => @seq.length
#
#    get: (pos) => @seq[pos]
#
#    position: (char) => @seq.indexOf(char)
#
#    insert: (wchar) => 
#
#  class Client
#    constructor: (@id) ->
#      @clock = 0
#
#  return (
#    WChar: Wchar
#    Client: Client
#  )