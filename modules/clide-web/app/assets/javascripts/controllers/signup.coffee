### @controller controllers:SignupController ###
define ['routes','util/md5'], (routes,md5) -> ($scope, $location, Console, Toasts, Auth) ->
  $scope.gravatar = null
  $scope.data =
    username: null
    email: null
    password: null
  $scope.updateGravatar = () -> if $scope.data.email?
    $scope.gravatar = md5($scope.data.email)
  $scope.signup = () ->    
    $scope.error = { }      
    Console.write "signing up as '#{$scope.username}'..."
    Auth.signup $scope.data,
      success: ->
        $location.path "/login"
        Toasts.push('success',"Welcome, your account has been created! :)")
      error: (data,status) ->
        switch status          
          when 400
            $scope.error = data
          when 404
            $scope.error[''] = 'the server did not respond'
          else
            $scope.error[''] = 'something went wrong...'
        