### @controller controllers:IdeController ###
define ['jquery'], ($) -> ($scope, $timeout, Files) ->
  $scope.start = () ->
    $scope.state = 'ide'
  $scope.state = 'login'
  $scope.sidebar = true
  $scope.files = Files

  to = null

  # This is very hacky and should be moved to a sidebar directive
  # in the future!
  $scope.select = (section) ->    
    $scope.sidebar = true
    $scope.sidebarSection = section
    top = $("#section-#{section}").position().top - 8
    currentST = $('#sidebarContent').scrollTop()    
    $('#sidebarContent').animate
      scrollTop: currentST + top