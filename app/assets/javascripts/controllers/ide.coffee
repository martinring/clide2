### @controller controllers:IdeController ###
define ['routes'], (routes) -> ($q, $scope, $timeout, $routeParams, Projects, Files, Dialog, Auth, Toasts, Session) ->  
  $scope.user = $routeParams.user  

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warn', 'You need to log in to view the requested resource!'
    return

  Auth.validateSession 
    success: (user) -> 
      if $routeParams.user isnt user.username
        $location.path '/login'
        Toasts.push 'warn', 'The requested resource is not associated with your user account!'
    error: -> 
      $location.path '/login'
      Toasts.push 'warn', 'Sorry, your login session has expired! Please enter your credentials once again.'    
  
  Session.open($routeParams.user, $routeParams.project)

  $scope.traffic = Session.traffic

  $scope.start = () ->
    $scope.state = 'ide'
  
  $scope.state = 'login'
  $scope.sidebar = true
  $scope.root = null
  $scope.openFiles = []
  $scope.currentFile = null

  Files.get($routeParams.user, $routeParams.project).then (root) ->      
    $scope.root = root
    console.log root

  $scope.selectFile = (file) -> unless file.files
    $scope.currentFile = file
    for f in $scope.openFiles
      return false if file is f
    $scope.openFiles.push(file)
    return true

  removeFromOpened = (file) ->
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

  $scope.closeFile = (file) ->
    file.close('confirm').then ->
      removeFromOpened(file)

  $scope.flatFiles = (prefix, where) ->
    result = []
    for file in where.files
      if file.files?
        flat = $scope.flatFiles("#{prefix}#{file.name}/",file)
        result.push flat...
      else
        file.prefix = prefix
        result.push file

  removeFile = (file) -> if file?
    if file.files?      
      removeFile(f) for f in file.files
    else if file.close?
      file.close()
      removeFromOpened(file)
    #recursive remove
    remove = (list) ->
      for f, i in list
        if f is file
          list.splice(i,1)
          return true
        if f.files?
          if remove(f.files)
            return true
      return false
    remove($scope.root.files)
    

  $scope.deleteFile = (file) ->    
    if file.files?
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete the folder '#{file.name}' and all of its content? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          Files.delete($routeParams.user,$routeParams.project,file.path).then ->            
            removeFile(file)
    else
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete '#{file.name}'? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          Files.delete($routeParams.user,$routeParams.project,file.path).then ->            
            removeFile(file)

  types = [
    { text: 'Isabelle Theory', ext: 'thy' }
    { text: 'Scala Class', ext: 'scala' }
  ]

  $scope.createFile = (folder) ->    
    Dialog.push
      title: 'new file'
      queries: [{ name: 'type', type: 'select', options: types, value: types[0] }, 'name']
      buttons: ['Ok','Cancel']
      done: (answer,result) -> if answer is 'Ok'
        file = 
          name: result.name
        Files.put($routeParams.user,$routeParams.project,folder.path,file).then (n) ->
          folder.files.push n        
          $scope.selectFile(n)

  $scope.createFolder = (folder) ->
    Dialog.push
      title: 'new folder'
      queries: ['name']
      buttons: ['Ok','Cancel']
      done: (answer,result) -> if answer is 'Ok'
        file =
          name: result.name
          files: []
        Files.put($routeParams.user,$routeParams.project,folder.path,file).then (n) ->                              
          folder.files.push n

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