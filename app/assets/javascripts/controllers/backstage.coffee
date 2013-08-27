### @controller clide.controllers:BackstageController ###
define ['util/md5'], (md5) -> ($scope, $location, $routeParams, $timeout, Projects, Console, Auth, Toasts, Dialog) ->
  $scope.user = $routeParams.user 

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warn', 'You need to log in to view the requested resource!'
    return

  Auth.validateSession 
    success: -> 
      if $scope.user isnt Auth.user?.username
        $location.path '/login'
        Toasts.push 'warn', 'The requested resource is not associated with your user account!'
      else
        $scope.email = Auth.user.email
        $scope.gravatar = md5(Auth.user.email)
    error: -> 
      $location.path '/login'
      Toasts.push 'warn', 'Sorry, your login session has expired! Please enter your credentials once again.'
  
  $scope.selectedProject = null

  $scope.change = (project) ->     
    $scope.selectedProject = project

  Projects.update $scope.user, (projects) ->    
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
    $location.path "/#{Auth.user.username}/#{$scope.selectedProject.name}/"    