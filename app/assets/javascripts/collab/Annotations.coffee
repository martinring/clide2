define ['collab/Operation'], (Operation) ->
  class Annotations
    constructor: () ->
      @current = []
      @buffered = ""

    transform: (op) ->
      @current