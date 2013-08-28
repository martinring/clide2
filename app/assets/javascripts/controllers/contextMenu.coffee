define () -> ($scope, ContextMenu) ->  
  $scope.contextmenu = ContextMenu
  $scope.done = (action) ->
    $('#contextmenu').blur()    
    action()