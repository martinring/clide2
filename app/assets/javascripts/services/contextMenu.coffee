### @service services:ContextMenu ###
define [], () -> ($timeout) ->  
  state = { current: null }
  state.display = (create, x, y) ->
    $('#contextmenu').css # HACK!
      left: x
      top: y    
    state.current = create
    $('#contextmenu').focus()
  return state