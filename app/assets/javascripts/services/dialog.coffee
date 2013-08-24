### @service services:Dialog ###
define [], () -> () ->
  console.log 'initializing dialog service'
  
  queue = []

  state = {}
  
  next = (action) ->
    done = -> 
      if queue.length > 0            
        config = queue.shift()
        state.show = true
        state.title = config.title
        state.message = config.message
        state.buttons = config.buttons
        state.queries = config.queries
        state.error = config.error
        state.wait = false
      else
        state.show = false
    if state.show
      result = { }
      state.wait = false
      switch typeof action
        when 'string' then switch action
          when 'Cancel' 
            done()
            return
          else console.error 'unrecognized action'
        else 
          for q in state.queries
            result[q.name] = q.value
          result.$wait = (task) ->            
            state.wait = true
            state.task = task
            return (
              success: done
              error: (e) -> 
                state.error = e
                state.wait = false
            )
          action(result)
    done() unless state.wait

  push = (config) ->
    for q in config.queries      
      q.type = q.type or 'text'
      q.text = q.text or q.name+':'
    config.buttons = config.buttons.map (button) -> 
      switch typeof button
        when 'string'
          switch button
            when 'Cancel'
              return { text: 'Cancel', action: () ->  }
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