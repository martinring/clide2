# RequireJS configuration
require.config
  #paths:    
  #  'angular':          'lib/angularjs/1.2.0rc1/angular'
  #  'angular-animate':  'lib/angularjs/1.2.0rc1/angular-animate'
  #  'angular-cookies':  'lib/angularjs/1.2.0rc1/angular-cookies'
  #  'angular-resource': 'lib/angularjs/1.2.0rc1/angular-resource'
  #  'angular-route':    'lib/angularjs/1.2.0rc1/angular-route'            
  #  'codemirror':       'lib/codemirror/3.16/lib/codemirror'
  shim:
    #'angular':
    #  exports: 'angular'      
    #'angular-animate':
    #  exports: 'angular'
    #  deps:    ['angular']
    #'angular-cookies':
    #  exports: 'angular'
    #  deps:    ['angular']
    #'angular-resource':
    #  exports: 'angular'
    #  deps:    ['angular']
    #'angular-route':
    #  exports: 'angular'
    #  deps:    ['angular']
    #'codemirror':
    #  exports: 'CodeMirror'
    'routes':
      exports: 'jsRoutes'
  #priority: [
  #  'angular' 
  #]

require ['app'], (app) ->     
  #TODO: MAKE THIS WORK AGAIN
  #app.run ($location, $rootScope, $q) ->
  #  $rootScope.$on '$routeChangeSuccess', (e,n,o) ->
  #    $rootScope.title = n.$$route.title
  angular.element(document).ready ->
    angular.bootstrap document, ['clide']
    angular.element(document.getElementById('loading')).remove()    