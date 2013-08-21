### @controller controllers:SignupController ###
define ['routes','underscore'], (routes,_) -> ($scope, $location, Console, Toasts, Auth) ->
  console.log 'initializing signup controller'
  $scope.data =
    username: null
    email: null
    password: null
  $scope.signup = () ->    
    $scope.signupForm.error = { }
    Console.write "signing up as '#{$scope.username}'..."    
    Auth.signup $scope.data,
      success: ->
        $location.path "/#{Auth.user.username}/backstage"
        Toasts.push('success',"You have been successfully logged in as #{Auth.user}!")
      error: (data,status) ->
        console.log data        
        switch status          
          when 400
            _.extend($scope.signupForm.error,data)
          when 404
            $scope.signupForm.error[''] = 'the server did not respond'
          else
            $scope.signupForm.error[''] = 'something went wrong...'
        