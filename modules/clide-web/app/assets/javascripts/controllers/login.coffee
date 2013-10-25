### @controller controllers:LoginController ###
define ['routes'], (routes) -> ($scope, $location, Auth, Toasts) ->
  $scope.data =
    username: null
    password: null
    staySignedIn: true
  $scope.login = () ->    
    $scope.error = { }
    Auth.login $scope.data,
      success: ->
        $location.path "/#{Auth.user.username}/backstage"
        Toasts.push('success',"You have been successfully logged in as #{Auth.user.username}!")
      error: (data,status) ->
        switch status
          when 401
            $scope.error = data
          when 404
            $scope.error[''] = 'the server did not respond'
          else
            $scope.error[''] = 'sorry, something is broken...'