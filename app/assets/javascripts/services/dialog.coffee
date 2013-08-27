### @service services:Dialog ###
define [], () -> () ->  
  queue = []

  state = { current: null }  
  
  next = (action) ->
    done = ->               
      if queue.length > 0        
        state.current = queue.shift()
      else
        state.current = null
    if state.current?
      result = { }
      state.current.wait = false
      if action
        if state.current.queries?
          for q in state.current.queries
            result[q.name] = q.value
        result.$wait = (task) ->            
          state.current.wait = true
          state.current.task = task
          return (
            success: done
            error: (e) -> 
              state.current.error = e
              state.current.wait = false
          )
        action(result)
    done() unless state?.wait

  push = (config) ->
    if state.current?
      queue.unshift state.current
      state.current = null
    if config.queries
      for q in config.queries
        q.type = q.type or 'text'
        q.text = q.text or q.name+':'
    config.buttons = config.buttons.map (button) -> 
      switch typeof button
        when 'string'          
          return { text: button, action: () -> config.done?(button) }
        when 'object'
          unless button.action?
            for name, action of button
              button.text = name
              button.action = action
          return button

    queue.unshift config

    next()

  state.push = push
  state.next = next

  return state