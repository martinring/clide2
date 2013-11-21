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

### @directive directives:tabs ###
define -> () ->
  restrict: 'E'
  transclude: true
  scope: {}
  controller: ($scope, $element) ->
    tabs = $scope.tabs = []
    $scope.select = (tab) ->
      angular.forEach tabs, (tab) ->
        tab.selected = false
      tab.selected = true
    $scope.close = (tab) ->
      tab.close() if tab.close?
      tabs.splice(tabs.indexOf(tab),1)
    @addTab = (tab) ->
      $scope.select(tab) if (tabs.length == 0)
      tabs.push(tab)
  template:
    '<div class="tabs">' +
      '<ul class="headers">' +
        '<li ng-repeat="tab in tabs" ng-class="{active:tab.selected}" ng-click="select(tab)">'+
          '{{tab.title}} <span class="icon" ng-click="close(tab)">&#xE089;</span>' +
        '</li>' +
      '</ul>' +
      '<div class="content" ng-transclude></div>' +
    '</div>'
  replace: true
