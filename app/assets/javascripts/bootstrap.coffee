require ['angular','jquery','app'], (angular, $) -> 
  $ -> 
    console.log 'Hallo'
    angular.bootstrap document, ['clide']        
    $('#loading').remove()