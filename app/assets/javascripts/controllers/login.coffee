define ['routes'], (routes) -> ($scope,$location,App,Console,Toasts) ->
  console.log 'initializing login controller'
  $scope.username = ''
  $scope.password = ''
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
        Toasts.push('success',"You have been successfully logged in as #{$scope.username}!")
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