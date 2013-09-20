define () -> ($scope, ContextMenu) ->  
  $scope.contextmenu = ContextMenu
  el = null
  $scope.done = (action) ->
    el = document.getElementById('contextmenu') unless el?    
    el.blur()
    action()