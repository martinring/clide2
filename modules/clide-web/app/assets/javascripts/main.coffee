# RequireJS configuration
require.config
  paths:
    'codemirror':         'vendor/codemirror/codemirror-compressed'
  shim:
    'codemirror':
      exports: 'CodeMirror'    
    'routes':
      exports: 'jsRoutes'


require ['app','util/fonts'], (app) ->
  app.run ($rootScope, Session, Files) ->
    $rootScope.$on '$routeChangeSuccess', (e,n,o) ->      
      $rootScope.title = n.$$route.title
      unless n.$$route.ide
        Files.close()
        Session.close()
        
  angular.element(document).ready ->
    angular.bootstrap document, ['clide-web']
    angular.element(document.getElementById('loading')).remove()