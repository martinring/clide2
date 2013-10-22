# RequireJS configuration
require.config
  paths:
    'codemirror': 'vendor/codemirror/codemirror'
    'codemirror-hs': 'vendor/codemirror/mode/haskell/haskell'
  shim:
    'codemirror':
      exports: 'CodeMirror'
    'codemirror-hs':
      deps: ['codemirror']
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