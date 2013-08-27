### @config ### 
define [], () -> ($routeProvider, $locationProvider, $httpProvider) ->
  $locationProvider.html5Mode(true)

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
  $routeProvider.when '/404',
    templateUrl: '/assets/partials/404.html'    
  $routeProvider.when '/401',
    templateUrl: '/assets/partials/401.html'        
  $routeProvider.otherwise
    redirectTo: '/404'

  #$httpProvider.defaults.transformRequest.unshift (data) ->
  #  console.log data    
  #  console.log 'request augmented with session key ' + localStorage['session']
  #  if data?
  #    if typeof data is 'string'
  #      data =
  #        $sessionKey: localStorage['session']
  #        data: data
  #    else
  #      data.$sessionKey = localStorage['session']
  #  else        
  #    data =
  #      $sessionKey: localStorage['session']
  #  console.log data
  #  return data

  #$httpProvider.interceptors.push ($q, $location, Toasts) ->
  #  responseError: (rejection) ->      
  #    switch rejection.status 
  #      when 400
  #        Toasts.push 'error', 'a communication error occured!'
  #    $q.reject(rejection)


  #$httpProvider.responseInterceptors.push ($location, $q) -> 
  #  success = (response) -> response
  #  error = (response) ->
  #    if response.status = 401
  #      $location.path('/login')
  #    $q.reject(response)      
  #  (promise) -> promise.then success, error