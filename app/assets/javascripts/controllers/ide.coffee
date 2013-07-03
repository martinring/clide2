define () -> ($scope, Files) ->
  console.log 'initialize ide'
  $scope.start = () ->
    $scope.state = 'ide'
  $scope.state = 'login'
  $scope.sidebar = true
  $scope.files = Files 