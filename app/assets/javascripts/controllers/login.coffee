### @controller controllers:LoginController ###
define ['routes','underscore'], (routes,underscore) -> ($scope, $location, Auth, Toasts) ->
  console.log 'initializing login controller'
  if Auth.loggedIn() # check if the user is already logged in
    Auth.validateSession 
      success: ->
        $location.path "/#{Auth.user.username}/backstage"  
  $scope.data =
    username: null
    password: null
    staySignedIn: true
  $scope.login = () ->
    console.log $scope.loginForm
    $scope.loginForm.error = { }
    Auth.login $scope.data,
      success: ->
        $location.path "/#{Auth.user.username}/backstage"
        Toasts.push('success',"You have been successfully logged in as #{Auth.user.username}!")
      error: (data,status) ->
        console.log data['']
        switch status
          when 400
            _.extend($scope.loginForm.error,data)
          when 404
            $scope.signupForm.error[''] = 'the server did not respond'
          else
            $scope.signupForm.error[''] = 'something went wrong...'