### @directive directives:contextMenu ###
define ['angular', 'jquery'], (angular, $) -> (ContextMenu) ->    
  link: (scope, iElement, iAttrs, controller) ->
    fun = iAttrs.contextMenu
    $(iElement[0]).bind 'contextmenu', (e) -> scope.$apply ->
      ContextMenu.display scope.$eval(fun),
        e.pageX, e.pageY
      false