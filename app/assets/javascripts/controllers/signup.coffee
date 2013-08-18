#>module
#>import routes
#>inject $scope $location App Console Toasts
console.log 'initializing signup controller'
$scope.username = ''
$scope.email = ''
$scope.password = ''  
$scope.signup = () ->    
  $scope.signupForm.error = null    
  App.wait = true
  Console.write "signing up as '#{$scope.username}'..."
  routes.controllers.Application.signup().ajax
    data: $('#signupForm').serialize()
    success: (data) ->
      App.loggedIn = true
      App.user = $scope.username
      Toasts.push 'success', 'your account has been created'
      $location.path "/login"
      App.wait = false
      $scope.$apply()
    error: (data) -> switch data.status
      when 400
        App.loggedIn = false
        $scope.signupForm.error = data.responseText
        Console.write data.responseText, 'failure'
        App.wait = false
        $scope.$apply()
      when 404
        App.loggedIn = false
        $scope.signupForm.error = 'The server did not respond'
        Console.write 'The server did not respont', 'failure'
        App.wait = false
        $scope.$apply()