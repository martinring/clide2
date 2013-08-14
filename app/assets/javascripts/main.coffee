# RequireJS configuration
require.config
  paths:    
    angular:           'lib/angularjs/1.1.5/angular'
    'angular-cookies': 'lib/angularjs/1.1.5/angular-cookies'
    codemirror:        'lib/codemirror/3.15/lib/codemirror'
    jquery:            'lib/jquery/2.0.2/jquery'
    typekit:           '//use.typekit.net/bzl6miy'
    underscore:        'lib/underscorejs/1.5.1/underscore'    
  shim:
    'angular-cookies':
      exports: 'angular'
      deps:    ['angular']
    angular:
      exports: 'angular'
      deps:    ['jquery']
    jquery:
      exports: 'jQuery'
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
require ['typekit', 'routes', 'bootstrap', 'config'], (Typekit, routes) -> 
  Typekit.load()