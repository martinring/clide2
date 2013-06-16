define ['angular','controllers/index','directives/index','filters/index','services/index'], (angular) ->
  angular.module 'clide', [
    'ui.state',
    'clide.controllers',
    'clide.directives',
    'clide.filters',
    'clide.services'
  ]