define -> (document) ->
  buffer = { }

  remove = (key) ->


  create = (key, own) ->
    widget = document.createElement("ul")
    widget.className = "autocomplete"


    buffer[key] = {
      remove: -> angular.element(widget).remove()
      add: (value) ->
    }

  {
    create: create
    remove: remove
  }
