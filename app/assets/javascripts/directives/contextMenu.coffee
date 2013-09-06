### @directive directives:contextMenu ###
define -> (ContextMenu) ->    
  link: (scope, iElement, iAttrs, controller) ->
    fun = iAttrs.contextMenu        
    iElement.bind 'contextmenu', (e) -> scope.$apply ->       
      ContextMenu.display scope.$eval(fun),
        e.pageX, e.pageY
      e.preventDefault()