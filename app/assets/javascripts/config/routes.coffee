define [], () -> ($routeProvider, $locationProvider) ->
  $locationProvider.html5Mode(true)

  console.log 'configuring routes'

  $routeProvider.when '/'      
    redirectTo: '/login'
  $routeProvider.when '/collab'      
    templateUrl: '/assets/partials/collab.html'    
    controller:  'CollabController'
  $routeProvider.when '/login'      
    templateUrl: '/assets/partials/login.html'
    controller:  'LoginController'
  $routeProvider.when '/signup'
    templateUrl: '/assets/partials/signup.html'
    controller:  'SignupController'
  $routeProvider.when '/:user/backstage'
    templateUrl: '/assets/partials/backstage.html'
    controller:  'BackstageController'
  $routeProvider.when '/:user/:project/',
    templateUrl: '/assets/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.when '/:user/:project/:file',
    templateUrl: '/assets/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.otherwise
    redirectTo: '/'