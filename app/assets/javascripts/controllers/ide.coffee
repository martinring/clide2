### @controller controllers:IdeController ###
define ['routes'], (routes) -> ($scope, $location, $routeParams, Dialog, Auth, Toasts, Session, Files) ->  
  $scope.user = $routeParams.user  

  $scope.path = 
    if $routeParams.path? and $routeParams isnt ''
      $routeParams.path.split('/')
    else []

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warning', 'You need to log in to view the requested resource!'
    return

  Files.init($routeParams.user, $routeParams.project)
  Files.explore($scope.path)

  Session.init($routeParams.user, $routeParams.project)

  $scope.session = Session.info
  $scope.files = Files.info

  $scope.browseTo = Files.browseTo
  $scope.currentDir = Files.current  

  $scope.reconnect = ->
    Files.init($routeParams.user, $routeParams.project)
    Files.explore($scope.path)

  $scope.start = () ->
    $scope.state = 'ide'
  
  $scope.sidebar = true
  $scope.root = null
  $scope.openFiles = []
  $scope.currentFile = null  

  $scope.selectFile = (file) ->
    $scope.selectedFile = file.id

  $scope.openFile = (file) ->
    if file.isDirectory
      $scope.browseTo(file.path)
    else          
      Session.openFile(file.id)

  $scope.closeFile = (id) ->
    Session.closeFile(id)
    
  $scope.deleteFile = (file) ->
    if file.isDirectory
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete the folder '#{file.path[file.path.length - 1]}' and all of its content? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          Files.delete(file.path)
    else
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete '#{file.path[file.path.length - 1]}'? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          Files.delete(file.path)

  types = [
    { text: 'Isabelle Theory', ext: 'thy' }
    { text: 'Scala Class', ext: 'scala' }
  ]

  $scope.createFile = (folder) ->    
    Dialog.push
      title: 'new file'
      queries: [{name: 'name', text: 'please enter a name for the new file:'}]
      buttons: ['Ok','Cancel']
      done: (answer,result) -> if answer is 'Ok'
        if result.name? and result.name.length > 0
          p = folder.path?.slice() or []
          p.push(result.name)
          Files.touchFile(p)
        else
          result.error = 'Please enter a name'

  $scope.createFolder = (folder) ->
    Dialog.push
      title: 'new folder'
      queries: [{name: 'name', text: 'please enter a name for the new folder:'}]
      buttons: ['Ok','Cancel']
      done: (answer,result) -> if answer is 'Ok'
        if result.name? and result.name.length > 0
          p = folder.path?.slice() or []
          p.push(result.name)
          Files.touchFolder(p)
        else
          result.error = 'Please enter a name'

  $scope.fileContextMenu = (file) ->
    if (file.files?) 
      file.expand = true
      [
        icon: 'plus'
        text: 'New File'
        action: -> $scope.createFile(file)
      ,
        icon: 'plus-sign-alt'
        text: 'New Folder'
        action: -> $scope.createFolder(file)
      ,
        icon: 'remove'
        text: 'Delete'
        action: -> $scope.deleteFile(file)
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
    #top = $("#section-#{section}").position().top - 8
    #currentST = $('#sidebarContent').scrollTop()    
    #$('#sidebarContent').animate
    #  scrollTop: currentST + top