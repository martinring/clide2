require ['angular','jquery','app'], (angular, $) -> 
  angular.element(document).ready ->
    angular.bootstrap document, ['clide']
    $('#loading').remove()