define ['angular', 'directives/editor','directives/tabs','directives/tab'], (angular, editor, tabs, tab) ->
  module = angular.module 'clide.directives', []
  module.directive 'editor', editor
  module.directive 'tabs', tabs
  module.directive 'tab', tab