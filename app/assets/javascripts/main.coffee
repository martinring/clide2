# RequireJS configuration
require.config
  shim:
    'routes':
      exports: 'jsRoutes'

require ['app'], (app) ->       
  app.run ($rootScope, Session, Files) ->
    $rootScope.$on '$routeChangeSuccess', (e,n,o) ->
      $rootScope.ide   = n.$$route.ide
      $rootScope.title = n.$$route.title
      unless n.$$route.ide
        Files.close()
        Session.close()
        
  angular.element(document).ready ->
    angular.bootstrap document, ['clide']
    angular.element(document.getElementById('loading')).remove()    