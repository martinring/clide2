define () -> () -> ($scope) ->
  $scope.start = () ->
    $scope.state = 'ide'
  $scope.state = 'login'