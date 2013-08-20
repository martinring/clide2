### @controller controllers:LoginController ###
define ['routes'], (routes) -> ($scope, $location, Auth, Toasts) ->
  console.log 'initializing login controller'
  $scope.data =
    username: null
    password: null
  $scope.login = () ->
    console.log $scope.loginForm
    $scope.loginForm.error = null        
    Auth.login $scope.data,
      success: ->
        $location.path "/#{Auth.user}/backstage"
        Toasts.push('success',"You have been successfully logged in as #{Auth.user}!")
      error: (data,status) ->
        console.log data['']
        switch status
          when 401
            $scope.loginForm.error = data['']
          when 404
            $scope.loginForm.error = 'The server did not respond'
