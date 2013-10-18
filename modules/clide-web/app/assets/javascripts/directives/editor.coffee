### @directive directives:editor ###
define ['routes','codemirror','codemirror-hs'], (routes,CodeMirror) -> () -> 
  restrict: 'E'
  transclude: true
  template: '<textarea></textarea>'
  replace: true

  scope: 
    document:    '&'
    lineNumbers: '&'
    readOnly:    '&'
    fontSize:    '&'
    font:        '&'

  link: (scope, iElem, iAttrs, controller) ->
    window.countMe = (window.countMe or 0) + 1

    cm = CodeMirror.fromTextArea iElem[0],
      undoDepth:   0 # disable

    window.cm = cm

    scope.$watch 'lineNumbers()', (n,o) ->      
      cm.setOption('lineNumbers', n)
      cm.refresh()

    scope.$watch 'readOnly()', (n,o) ->      
      cm.setOption('readOnly',n or false)

    scope.$watch 'font()', (n,o) ->      
      cm.getWrapperElement().style.fontFamily = n
      cm.refresh()

    scope.$watch 'fontSize()', (n,o) ->
      console.log n
      cm.getWrapperElement().style.fontSize = n + 'pt'
      cm.refresh()
          
    scope.$watch 'document()', (n,o) ->       
      if n? then cm.swapDoc(n) else cm.swapDoc(CodeMirror.Doc(""))