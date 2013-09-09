# RequireJS configuration
require.config
  shim:
    'routes':
      exports: 'jsRoutes'

require ['app'], (app) ->       
  app.run ($rootScope) ->
    $rootScope.$on '$routeChangeSuccess', (e,n,o) ->
      $rootScope.ide   = n.$$route.ide
      $rootScope.title = n.$$route.title
  angular.element(document).ready ->
    angular.bootstrap document, ['clide']
    angular.element(document.getElementById('loading')).remove()    