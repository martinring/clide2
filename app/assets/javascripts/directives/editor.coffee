### @directive directives:editor ###
define ['routes','collab/Operation','collab/CodeMirror','collab/Client','collab/AnnotationStream'], (routes,Operation,CMAdapter,Client,AnnotationStream) -> (Dialog,Session,$timeout,$q) -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],      
      lineNumbers: true      
      undoDepth: 0 # disable      

    scope.$watch (-> scope.$eval(iAttrs.file)), (n,o) -> if n?
      console.log n