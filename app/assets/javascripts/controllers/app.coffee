### @controller controllers:AppController ###
define -> ($scope, $location, Auth, Toasts, version) ->  
  $scope.user = Auth.user
  $scope.version = version
  $scope.goBack = () ->
    window.history.back();
  $scope.logout = () ->
    Auth.logout 
      success: ->
        $location.path '/login'
        Toasts.push 'success', 'You have been logged out!'
      error: ->
        Toasts.push 'danger', 'There was an error while logging out!'
    