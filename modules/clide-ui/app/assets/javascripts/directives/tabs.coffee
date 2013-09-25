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