define () -> ($scope, $location, App, Console, Toasts, Dialog) ->
  console.log 'initialzing app controller'
  $scope.app = App
  $scope.console = Console
  $scope.toasts = Toasts.toasts
  $scope.dialog = Dialog
  $scope.cm = 
  $scope.goBack = () ->
    window.history.back();