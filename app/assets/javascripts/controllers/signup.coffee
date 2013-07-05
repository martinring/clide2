define () -> ($scope,$location,App,Console) ->
  $scope.email = ''
  $scope.password = ''
  $scope.login = () ->
    Console.write "signing up as #{$scope.username}..."    
    App.wait = true
    done = () ->
      $location.path "/#{$scope.username}/backstage"
      App.user = $scope.username
      App.loggedIn = true
      App.wait = false
      $scope.$apply()
    setTimeout(done,1000)