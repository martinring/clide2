# RequireJS configuration
require.config
  paths:    
    angular:    'lib/angular/angular.min'    
    router:     'lib/angular/angular-ui-router.min'
    codemirror: 'lib/codemirror/codemirror'
    jquery:     'lib/jquery/jquery'
    domReady:   'lib/require/domReady'
    typekit:    '//use.typekit.net/bzl6miy'
    underscore: 'lib/underscore/underscore'
  shim:
    router:
      deps: ['angular']
    angular:
      exports: 'angular'     
    codemirror:
      exports: 'CodeMirror'
    typekit:
      exports: 'Typekit'
    underscore:
      exports: '_'
    routes:
      exports: 'jsRoutes'    
  priority: [
    'angular'
  ]    

# Initialize Fonts
require ['angular', 'typekit', 'app', 'bootstrap', 'router'], (angular, Typekit, app) -> 
  Typekit.load()
  app.config ($stateProvider, $routeProvider, $locationProvider) ->
    $locationProvider.html5Mode(true)

    $stateProvider.state 'index',
      url: '/'
      views: 
        root: 
          templateUrl: 'assets/partials/backstage.html'
    $stateProvider.state 'ide',
      url: '/ide'
      views:
        root:
          templateUrl: 'assets/partials/ide.html'