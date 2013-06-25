define () -> ($scope,$location,App,Console) ->
  $scope.email = ''
  $scope.password = ''
  $scope.password2 = ''
  $scope.checkPassword = () ->
    $scope.signupForm.password2.$error.dontMatch = $scope.password isnt $scope.repeatPassword
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