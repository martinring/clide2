require ['angular','jquery','app'], (angular, $) -> 
  $ ->     
    angular.bootstrap document, ['clide']        
    $('#loading').remove()