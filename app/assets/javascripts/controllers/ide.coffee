### @controller controllers:IdeController ###
define ['jquery'], ($) -> ($scope, $timeout, Files, Dialog) ->
  $scope.start = () ->
    $scope.state = 'ide'
  $scope.state = 'login'
  $scope.sidebar = true
  $scope.files = Files.files
  $scope.openFiles = []
  $scope.currentFile = null

  $scope.selectFile = (file) -> unless file.files
    $scope.currentFile = file
    for f in $scope.openFiles
      return false if file is f
    $scope.openFiles.push(file)
    console.log($scope.openFiles)
    return true

  $scope.fileContextMenu = (file) ->
    if (file.files?) then [
      icon: 'plus'
      text: 'New File'
      action: ->
        submit = (result) ->
          nfile = 
            name: result.name
            type: 'thy'
            icon: 'icon-file-alt'
          file.files.push nfile
          $scope.selectFile(nfile)
        Dialog.push
          title: 'new file'
          queries: ['name']
          buttons: [{ 'Ok': submit },'Cancel']
    ]
    else [
      icon: 'folder-open'
      text: 'Open'
      action: -> $scope.selectFile(file)
    ]


  # This is very hacky and should be moved to a sidebar directive
  # in the future!
  $scope.select = (section) ->    
    $scope.sidebar = true
    $scope.sidebarSection = section
    top = $("#section-#{section}").position().top - 8
    currentST = $('#sidebarContent').scrollTop()    
    $('#sidebarContent').animate
      scrollTop: currentST + top