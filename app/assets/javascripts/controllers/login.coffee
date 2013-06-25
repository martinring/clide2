define () -> ($scope,$location,App,Console) ->
  $scope.username = 'martinring'
  $scope.password = 'gNurz431'
  $scope.login = () ->
    Console.write "logging in as #{$scope.username}..."    
    App.wait = true
    done = () ->    
      $location.path "/#{$scope.username}/backstage"
      App.user = $scope.username
      App.loggedIn = true
      App.wait = false
      $scope.$apply()
    setTimeout(done,1000)