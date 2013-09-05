### @directive directives:sidebar ###
define -> () ->   
  restrict: 'E'
  transclude: true
  scope: {}
  controller: ($scope, $element) -> 
    sections = $scope.sections = []
    $scope.select = (section) ->      
      angular.forEach sections, (section) ->
        section.selected = false
      section.selected = true
    @addSection = (section) ->
      $scope.select(section) if (sections.length == 0)
      sections.push(section)
  template: """
<nav id="ribbon">
  <ul class="nav menu" ng-init='sidebarSection="files"'>
    <li title='Files' ng-click='sidebarSection="files";sidebar=true' ng-class='{active: sidebarSection=="files"}'>&#xe011;</li>
    <li title='Edit' ng-click='sidebarSection="edit";sidebar=true' ng-class='{active: sidebarSection=="edit"}'>&#xe002;</li>
    <li title='View' ng-click='sidebarSection="view";sidebar=true' ng-class='{active: sidebarSection=="view"}'>&#xe062;</li>
    <li title='Settings' ng-click='sidebarSection="settings";sidebar=true' ng-class='{active: sidebarSection=="settings"}'>&#xe04A;</li>
    <li title='Help' ng-click='sidebarSection="help";sidebar=true' ng-class='{active: sidebarSection=="help"}'>&#xe085;</li>        
  </ul>
  <div id="sidebarButton" ng-click='sidebar=!sidebar'>&#xE093;</div>
</nav>"""

  replace: true