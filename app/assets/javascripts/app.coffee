define ['angular','angular-cookies','controllers','directives','filters','services'], (angular) ->
  angular.module 'clide', [
    'clide.controllers',
    'clide.directives',
    'clide.filters',
    'clide.services',
    'ngCookies' #allow access to cookie data without page refreshes
  ]