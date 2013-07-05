define () -> ($scope, $location, App, Console) ->
  $scope.app = App
  $scope.console = Console
  $scope.goBack = () ->
    window.history.back();