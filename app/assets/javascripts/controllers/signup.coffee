### @controller controllers:SignupController ###
define ['routes','underscore','util/md5'], (routes,_,md5) -> ($scope, $location, Console, Toasts, Auth) ->
  $scope.gravatar = null
  $scope.data =
    username: null
    email: null
    password: null
  $scope.updateGravatar = () -> if $scope.data.email?
    $scope.gravatar = md5($scope.data.email)
  $scope.signup = () ->    
    $scope.signupForm.error = { }      
    Console.write "signing up as '#{$scope.username}'..."
    Auth.signup $scope.data,
      success: ->
        $location.path "/login"
        Toasts.push('success',"Welcome, your account has been created! :)")
      error: (data,status) ->
        console.log data
        switch status          
          when 400
            _.extend($scope.signupForm.error,data)
          when 404
            $scope.signupForm.error[''] = 'the server did not respond'
          else
            $scope.signupForm.error[''] = 'something went wrong...'
        