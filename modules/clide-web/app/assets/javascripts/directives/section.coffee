### @directive directives:section ###
define () -> () ->      
  require: '^sidebar'
  restrict: 'E'
  transclude: true
  scope: { title: '@' },
  link: (scope, element, attrs, sidebar) ->
    sidebar.addSection(scope)
    console.log(attrs)    
  template: """
<div class="tab" ng-class="{active: selected}" ng-transclude>
</div>"""
  replace: true
