### @controller controllers:BackstageController ###
define -> ($scope, $location, $routeParams, Projects, Console, Auth, Toasts) ->
  if $routeParams.user isnt Auth.user?.username
    $location.path '/login'
    Toasts.push 'warn', 'The requested resource does not belong to you!'
  console.log 'initializing backstage controller'
  $scope.projects = Projects
  $scope.start = () ->
    Toasts.push 'info', "preparing project '#{Projects.projects[Projects.current].name}'"    
    done3 = () ->    
      $location.path "/#{Auth.user.username}/#{Projects.projects[Projects.current].name}/"
      $scope.$apply()
    done2 = () -> 
      Toasts.push 'info', "Welcome to Isabelle/HOL (Isabelle2012: May 2012)"
      $scope.$apply()
      setTimeout(done3,500)
    done = () -> 
      Toasts.push 'info', "loaded project structure"
      $scope.$apply()
      setTimeout(done2,1000)
    setTimeout(done,1500)