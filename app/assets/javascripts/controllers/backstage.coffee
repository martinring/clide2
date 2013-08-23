### @controller controllers:BackstageController ###
define -> ($scope, $location, $routeParams, $timeout, Projects, Console, Auth, Toasts, Dialog) ->
  user = $routeParams.user

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warn', 'You need to log in to view the requested resource!'
    return

  Auth.validateSession
    success: -> if user isnt Auth.user?.username
      console.log user, Auth.user
      $location.path '/login'
      Toasts.push 'warn', 'The requested resource is not associated with your user account!'
    error: ->
      $location.path '/login'
      Toasts.push 'warn', 'Sorry, your login session has expired! Please enter your credentials once again.'
  
  $scope.selectedProject = null

  $scope.change = (project) ->     
    $scope.selectedProject = project

  Projects.update user, (projects) ->    
    $scope.projects = projects    

  $scope.logout = () ->
    Auth.logout
      success: ->
        $location.path '/login'
        Toasts.push 'success', 'You have been logged out!'
      error: ->
        Toasts.push 'warn', 'There was an error while loggin out!'

  $scope.createProject = (name,description,error) ->
    submit = (result) ->      
      promise = result.$wait('your project is beeing created')
      Projects.create Auth.user.username, result,
        success: promise.success
        error: promise.error
    Dialog.push
      error: error
      title: 'new project'
      queries: [
        { name: 'name', value: name }
          name: 'description'
          type: 'textarea'
          value: description
      ]
      buttons: [ { 'Ok': submit }, 'Cancel' ]

  $scope.start = () ->
    Toasts.push 'info', "preparing project '#{$scope.selectedProject.name}'"
    done3 = () ->    
      $location.path "/#{Auth.user.username}/#{$scope.selectedProject.name}/"
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