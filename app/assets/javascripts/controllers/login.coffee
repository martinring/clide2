define ['routes'], (routes) -> ($scope,$location,App,Console) ->
  $scope.username = 'martinring'
  $scope.password = 'gNurz431'
  $scope.login = () ->
    $scope.loginForm.error = null    
    App.wait = true
    Console.write "logging in as '#{$scope.username}'..."    
    routes.controllers.Application.login().ajax      
      data: $('#loginForm').serialize()
      success: (data) ->
        App.loggedIn = true 
        App.user = $scope.username       
        Console.write data, 'success'                
        $location.path "/#{$scope.username}/backstage"
        App.wait = false        
        $scope.$apply()
      error: (data) -> switch data.status
        when 400          
          App.loggedIn = false
          $scope.loginForm.error = data.responseText        
          Console.write data.responseText, 'failure'
          App.wait = false
          $scope.$apply()
        when 404       
          App.loggedIn = false
          $scope.loginForm.error = 'The server did not respond'
          Console.write 'The server did not respont', 'failure'
          App.wait = false
          $scope.$apply()        