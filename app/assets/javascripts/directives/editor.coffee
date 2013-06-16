# usage:
# <editor file="{path}"/>
define ['codemirror'], (CodeMirror) -> () -> 
  restrict: 'E'
  transclude: true
  controller: ($scope, $element) ->
    null
  scope: {}
  template: '<textarea ng-transclude></textarea>'
  replace: true
  link: (scope, iElem, iAttrs, controller) -> 
    scope.cm = CodeMirror.fromTextArea iElem[0],
      value: iElem[0].innerText
      lineNumbers: true      