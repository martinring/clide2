define () -> ($scope, $location, App, Console) ->
  $scope.app = App
  $scope.console = Console
  $scope.cm = 
  $scope.goBack = () ->
    window.history.back();