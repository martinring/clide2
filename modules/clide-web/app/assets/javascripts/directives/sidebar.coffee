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
