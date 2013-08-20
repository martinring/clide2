### @controller controllers:SignupController ###
define ['routes'], (routes) -> ($scope, $location, Console, Toasts, Auth) ->
  console.log 'initializing signup controller'
  $scope.data =
    username: null
    email: null
    password: null
  $scope.signup = () ->    
    $scope.signupForm.error = null    
    Console.write "signing up as '#{$scope.username}'..."    
    Auth.signup $scope.data,
      success: ->
        $location.path "/#{Auth.user}/backstage"
        Toasts.push('success',"You have been successfully logged in as #{Auth.user}!")
      error: (data,status) ->
        console.log data
        switch status
          when 401
            $scope.loginForm.error = data['']            
          when 404
            $scope.loginForm.error = 'The server did not respond'