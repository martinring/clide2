#>module
#>inject $scope, $location, App, Projects, Console
console.log 'initializing backstage controller'
$scope.projects = Projects
$scope.start = () ->
  Console.write "preparing project '#{Projects.projects[Projects.current].name}'"    
  App.wait = true
  done3 = () ->    
    $location.path "/#{App.username}/#{Projects.projects[Projects.current]}/"
    App.wait = false
    $scope.$apply()
  done2 = () -> 
    Console.write "Welcome to Isabelle/HOL (Isabelle2012: May 2012)"
    $scope.$apply()
    setTimeout(done3,500)
  done = () -> 
    Console.write "loaded project structure"
    $scope.$apply()
    setTimeout(done2,1000)
  setTimeout(done,1500)    