define () -> ($scope, Files) ->
  console.log 'initializing ide controller'  
  $scope.start = () ->
    $scope.state = 'ide'
  $scope.state = 'login'
  $scope.sidebar = true
  $scope.files = Files 