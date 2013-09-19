### @directive directives:editor ###
define ['routes'], (routes) -> () -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  scope: 
    document: '&'
    lineNumbers: '&'
    readOnly: '&'    

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],
      undoDepth:   0 # disable      

    scope.$watch 'lineNumbers()', (n,o) ->
      console.log 'lineNumbers:', n
      cm.setOption('lineNumbers',n or true)
      cm.refresh()

    scope.$watch 'readOnly()', (n,o) ->
      console.log 'readOnly:', n
      cm.setOption('readOnly',n or false)      
          
    scope.$watch 'document()', (n,o) -> 
      console.log n
      if n? then cm.swapDoc(n) else cm.swapDoc(CodeMirror.Doc(""))