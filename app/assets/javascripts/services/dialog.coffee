### @service services:Dialog ###
define [], () -> () ->  
  queue = []

  state = { current: null }
  
  next = (action) ->
    done = ->      
      state.current = queue.splice(0,1)[0]      

    if state.current?
      result = { }
      state.current.wait = false
      if action
        if state.current.queries?
          for q in state.current.queries
            result[q.name] = q.value
        res = action(result)
        switch typeof res
          when 'function'
            done(); res()
          when 'object'
            if res.then?
              res.then done, (error) ->
                state.current.error = error
            else done()
          when 'boolean'
            done() if res
          when 'string'
            state.current.error = res
          else done()

  # the dialog config object can set the following fields
  #  - title:   the header to display
  #  - text:    a message to display
  #  - queries: an array of queries (see below)
  #  - buttons: an array of buttons (defaults to just an 'Ok' button) (see below)
  #  - done:    an optional function to be called when the user presses
  #             a button which does not have an action defined.
  push = (config) ->
    if state.current?
      queue.unshift state.current
      state.current = null
    # queries are objects with the fields
    #  - type: type of input to display (default is text)
    #  - name: identifier of the query
    #  - text: human readable title (default is same as name)
    #  - value: can be preset (default is null)
    #
    # all queries are transformed:
    #  - strings are short for a text query with name and text
    #    defined by its content
    #  - objects can leave out the type and text fields which are
    #    set to the default values described above
    config.queries = config.queries?.map (q) ->
      switch typeof q
        when 'string'
          return (
            type: 'text'
            text: q+':'
            name: q
          )
        when 'object'          
          q.type = q.type or 'text'
          q.text = q.text or q.name+':'
          return q
    config.buttons = config.buttons or ['Ok']
    # buttons are objects with the fields
    #  - name: the name of the button
    #  - text: human readable text on the button (defaults to name)
    #  - action: a function to be called when the button gets pressed (optional)
    #
    # all buttons are transformed:
    #  - strings are short for a button with text and name set to the value
    #    and no action
    #  - objects can be defined as { text/name: action }
    config.buttons = config.buttons.map (button) -> 
      switch typeof button
        when 'string'
          return { text: button, action: (result) -> config.done?(button,result) }
        when 'object'
          unless button.action?
            for name, action of button
              button.text = name
              button.action = action
          return button
    # if there is already a dialog being displayed, we prepend it to the queue      
    if state.current?      
      queue.unshift(state.current)
    # set the config as the current dialog
    state.current = config

  state.push = push
  state.next = next
  return state