### @directive directives:editor ###
define ['routes','codemirror','modes/isabelle'], (routes) ->   
  # TODO: Move somewhere else...    
  CodeMirror.commands.autocomplete = (cm) ->
    CodeMirror.showHint(cm,'anyword')

  () ->      
    restrict: 'E'
    transclude: true
    template: '<textarea></textarea>'
    replace: true

    scope: 
      document:    '&'
      tabSize:     '&'      
      lineNumbers: '&'
      readOnly:    '&'
      fontSize:    '&'
      font:        '&'
      annotations: '&'

    link: (scope, iElem, iAttrs, controller) ->
      window.countMe = (window.countMe or 0) + 1

      cm = CodeMirror.fromTextArea iElem[0],
        undoDepth:   0 # disable
        indentWithTabs: false
        tabSize: 2
        gutters: ['CodeMirror-foldgutter','CodeMirror-linenumbers']
        foldGutter: true
        extraKeys: 
          'Ctrl-Space':   'autocomplete'
          'Shift-Ctrl-C': 'toggleComment'          

      scope.$watch 'lineNumbers()', (n,o) ->      
        cm.setOption('lineNumbers', n)
        cm.refresh()

      scope.$watch 'readOnly()', (n,o) ->      
        cm.setOption('readOnly',n or false)

      scope.$watch 'font()', (n,o) ->      
        cm.getWrapperElement().style.fontFamily = n
        cm.refresh()

      scope.$watch 'fontSize()', (n,o) ->        
        cm.getWrapperElement().style.fontSize = n + 'pt'
        cm.refresh()

      scope.$watch 'tabSize()', (n,o) ->
        cm.setOption('tabSize',n or 2)

      scope.$watch 'annotations()', (n,o) ->
        # TODO: Switch annotations on and off
            
      scope.$watch 'document()', (n,o) ->       
        if n? then cm.swapDoc(n) else cm.swapDoc(CodeMirror.Doc(""))    