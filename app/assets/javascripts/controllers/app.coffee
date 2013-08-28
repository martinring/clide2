### @controller controllers:AppController ###
define -> ($scope, $location, Auth, version) ->  
  $scope.user = Auth.user
  $scope.version = version
  $scope.goBack = () ->
    window.history.back();