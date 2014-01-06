##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU Lesser General Public License as           ##
##   published by the Free Software Foundation, either version 3 of           ##
##   the License, or (at your option) any later version.                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU Lesser General Public         ##
##   License along with Clide.                                                ##
##   If not, see <http://www.gnu.org/licenses/>.                              ##
##                                                                            ##

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
        fixedGutter: false
        viewportMargin: 20 # for smoother scrolling on tablets
        extraKeys:
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
