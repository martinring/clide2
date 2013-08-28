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
    return true

  $scope.closeFile = (file) -> unless file.files
    i = $scope.openFiles.indexOf(file)    
    if i >= 0
      if (file is $scope.currentFile)
        if i > 0
          $scope.currentFile = $scope.openFiles[i-1]
        else if i is 0 and $scope.openFiles.length > 1
          $scope.currentFile = $scope.openFiles[1]
        else
          $scope.currentFile = null
      $scope.openFiles.splice(i,1)

  types = [
    { text: 'Isabelle Theory', ext: 'thy' }
    { text: 'Scala Class', ext: 'scala' }
  ]

  $scope.createFile = (folder) ->
    submit = (result) ->
      nfile = 
        name: result.name
        type: result.type.ext
        icon: 'icon-file-alt'          
      folder.files.push nfile
      $scope.selectFile(nfile)
    Dialog.push
      title: 'new file'
      queries: [{ name: 'type', type: 'select', options: types, value: types[0] }, 'name']
      buttons: [{ 'Ok': submit },'Cancel']
  
  $scope.fileContextMenu = (file) ->
    if (file.files?) 
      file.expand = true
      [
        icon: 'plus'
        text: 'New File'
        action: -> $scope.createFile(file)
      ]
    else 
      openOrClose = if $scope.openFiles.indexOf(file) >= 0      
          icon: null
          text: 'Close'
          action: -> $scope.closeFile(file)
        else
          icon: 'edit'
          text: 'Open'
          action: -> $scope.selectFile(file)
      [ openOrClose,    
        icon: 'remove'
        text: 'Delete'
        action: -> $scope.deleteFile(file)
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