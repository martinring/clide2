### @controller controllers:IdeController ###
define ['routes'], (routes) -> ($scope, $location, $routeParams, Dialog, Auth, Toasts, Session, Files) ->    
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

  $scope.reconnectSession = ->
    Session.init($routeParams.user, $routeParams.project)    

  $scope.start = () ->
    $scope.state = 'ide'
  
  $scope.sidebar = true
  $scope.root = null
  $scope.openFiles = []
  $scope.currentFile = null  

  $scope.selectFile = (file) ->
    $scope.selectedFile = file.id

  $scope.invite = () ->
    Dialog.push
      title: "invite a collaborator"
      text:  "note that you can not only invite other users but also non-human collaborators that can assist you. You might want to try 'isabelle' for instance."
      queries: ['username']
      buttons: ['Ok','Cancel']
      done: (answer, result) -> if (answer is 'Ok')
        Session.invite(result.username)

  $scope.openFile = (file) ->
    if file.isDirectory
      file.loading = true
      $scope.browseTo(file.path, file.id)
    else
      Session.openFile(file.id or file)

  $scope.setColor = (color) ->
    Session.setColor(color)

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
    if (file.isDirectory) 
      file.expand = true
      [       
        icon: 'folder-open'
        text: 'Open'
        action: -> $scope.openFile(file)      
      ,
        icon: 'trash'
        text: 'Delete'
        action: -> $scope.deleteFile(file)
      ]
    else 
      openOrClose = if $scope.session.activeFileId is file.id     
          icon: 'remove'
          text: 'Close'
          action: -> $scope.closeFile(file.id)
        else
          icon: 'edit'
          text: 'Edit'
          action: -> $scope.openFile(file)
      [ openOrClose,
        icon: 'trash'
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