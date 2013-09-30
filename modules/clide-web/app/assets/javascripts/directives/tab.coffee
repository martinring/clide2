### @directive directives:tab ###
define () -> () ->      
  require: '^tabs'
  restrict: 'E'
  transclude: true
  scope: { title: '@' },
  link: (scope, element, attrs, tabsCtrl) ->
    tabsCtrl.addTab(scope)
    console.log(attrs)
    scope.close = attrs.close if attrs.close?
  template:
    '<div class="tab" ng-class="{active: selected}" ng-transclude>'+
    '</div>'
  replace: true
