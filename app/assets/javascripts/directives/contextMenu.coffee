### @directive directives:contextMenu ###
define -> (ContextMenu) ->    
  link: (scope, iElement, iAttrs, controller) ->
    fun = iAttrs.contextMenu
    # TODO: MAKE THIS WORK AGAIN
    #$(iElement[0]).bind 'contextmenu', (e) -> scope.$apply ->
    #  ContextMenu.display scope.$eval(fun),
    #    e.pageX, e.pageY
    #  false