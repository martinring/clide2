define [], () -> ($routeProvider, $locationProvider) ->
  $locationProvider.html5Mode(true)

  $routeProvider.when '/'      
    redirectTo: '/login'
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