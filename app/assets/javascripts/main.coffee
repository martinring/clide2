# RequireJS configuration
require.config
  paths:    
    'angular':          'lib/angularjs/1.2.0rc1/angular'
    'angular-animate':  'lib/angularjs/1.2.0rc1/angular-animate'
    'angular-cookies':  'lib/angularjs/1.2.0rc1/angular-cookies'
    'angular-resource': 'lib/angularjs/1.2.0rc1/angular-resource'
    'angular-route':    'lib/angularjs/1.2.0rc1/angular-route'        
    'jquery':           'lib/jquery/2.0.3/jquery'
    'codemirror':       'lib/codemirror/3.16/lib/codemirror'
    'typekit':          '//use.typekit.net/bzl6miy'
    'underscore':       'lib/underscorejs/1.5.1/underscore'    
  shim:
    'angular':
      exports: 'angular'
      deps:    ['jquery']
    'angular-animate':
      exports: 'angular'
      deps:    ['angular']            
    'angular-cookies':
      exports: 'angular'
      deps:    ['angular']
    'angular-resource':
      exports: 'angular'
      deps:    ['angular']
    'angular-route':
      exports: 'angular'
      deps:    ['angular']
    'jquery':
      exports: 'jQuery'
    'codemirror':
      exports: 'CodeMirror'
    'typekit':
      exports: 'Typekit'
    'underscore':
      exports: '_'
    'routes':
      exports: 'jsRoutes'
  priority: [
    'angular' 
  ]

require ['typekit', 'angular', 'app'], (Typekit, angular, app) -> 
  console.log 'initializing typekit fonts'
  Typekit.load()
  angular.element(document).ready ->
    angular.bootstrap document, ['clide']
    $('#loading').remove()