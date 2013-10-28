### @config ### 
define ['routes'], (routes) -> ($routeProvider, $locationProvider) ->
  $locationProvider.html5Mode(true)

  $routeProvider.when '/'  
    redirectTo: '/login'
  $routeProvider.when '/login'
    title:       'login'
    templateUrl: '/client/partials/login.html'
    controller:  'LoginController'
  $routeProvider.when '/signup'
    title:       'signup'
    templateUrl: '/client/partials/signup.html'
    controller:  'SignupController'
  $routeProvider.when '/admin'
    title:       'admin'
    templateUrl: '/client/partials/admin.html'
    controller:  'AdminController'
  $routeProvider.when '/:user/backstage'
    title:       'backstage'
    templateUrl: '/client/partials/backstage.html'
    controller:  'BackstageController'  
  $routeProvider.when '/:user/:project',
    title:       'coding'
    ide:         true
    templateUrl: '/client/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.when '/:user/:project/:path*',
    title:       'coding'
    ide:         true
    templateUrl: '/client/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.when '/404',
    title:       'not found'
    templateUrl: '/client/partials/404.html'    
  $routeProvider.when '/401',
    title:       'not authorized'
    templateUrl: '/client/partials/401.html'        
  $routeProvider.otherwise
    redirectTo: '/404'