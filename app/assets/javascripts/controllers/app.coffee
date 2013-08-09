define () -> ($scope, $location, App, Console, Toasts) ->
  $scope.app = App
  $scope.console = Console
  $scope.toasts = Toasts.toasts
  $scope.cm = 
  $scope.goBack = () ->
    window.history.back();