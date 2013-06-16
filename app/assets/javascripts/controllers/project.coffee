define () -> () -> ($scope, Files) ->
  $scope.files = Files.files

  $scope.openFiles =
    [Files[0]]  

  $scope.close = (file) ->
    console.log(file)

  $scope.sidebar = true
  
  $scope.output = false