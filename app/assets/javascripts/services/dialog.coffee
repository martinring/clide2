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
        state.title = null
        state.message = null
        state.buttons = []
        state.queries = []
        state.error = null
        state.wait = false
    if state.show
      result = {}
      state.wait = false
      for q in state.queries
        result[q.name] = q.value
      result.wait = () ->
        state.wait = true
        return (
          success: done
          error: (e) -> state.error = e
        )
      action(result)
    done() unless state.wait

  create = (config) ->    
    queue.unshift config
    next()  

  state.create = create
  state.next = next

  return state