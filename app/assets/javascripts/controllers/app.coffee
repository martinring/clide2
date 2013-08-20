### @controller controllers:AppController ###
define -> ($scope, $location, Console, Toasts, Dialog, Auth) ->
  console.log 'initializing app controller'  
  $scope.console = Console
  $scope.toasts = Toasts.toasts
  $scope.dialog = Dialog
  $scope.auth = Auth
  $scope.cm = 
  $scope.goBack = () ->
    window.history.back();