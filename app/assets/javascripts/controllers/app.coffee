### @controller controllers:AppController ###
define -> ($scope, $location, Console, Toasts, Dialog, Auth, version) ->
  console.log 'initializing app controller'  
  $scope.console = Console
  $scope.toasts = Toasts.toasts
  $scope.dialog = Dialog
  $scope.auth = Auth
  $scope.version = version
  $scope.goBack = () ->
    window.history.back();