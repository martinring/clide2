# RequireJS configuration
require.config
  shim:
    'routes':
      exports: 'jsRoutes'

require ['app','collaboration/Operation','collaboration/Annotations'], (app,Operation,Annotation) ->
  op    = new Operation().retain(2).insert('__').retain(2).delete(4).retain(2).insert('__').retain(2)
  annon = new Annotation().plain(2).annotate(1,'before').plain(2).annotate(2,'inside_after').plain(1)
  
  console.log annon.transform(op).annotations  

  #app.run ($rootScope, Session, Files) ->
  #  $rootScope.$on '$routeChangeSuccess', (e,n,o) ->
  #    $rootScope.ide   = n.$$route.ide
  #    $rootScope.title = n.$$route.title
  #    unless n.$$route.ide
  #      Files.close()
  #      Session.close()
  #      
  #angular.element(document).ready ->
  #  angular.bootstrap document, ['clide']
  #  angular.element(document.getElementById('loading')).remove()    