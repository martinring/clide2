define ['angular', 'directives/editor','directives/tabs','directives/tab','directives/dialog'], (angular, editor, tabs, tab, dialog) ->
  module = angular.module 'clide.directives', []
  module.directive 'editor', editor
  module.directive 'dialog', dialog  