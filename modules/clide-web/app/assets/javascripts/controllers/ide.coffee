##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU General Public License as published by     ##
##   the Free Software Foundation, either version 3 of the License, or        ##
##   (at your option) any later version.                                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU General Public License        ##
##   along with Clide.  If not, see <http://www.gnu.org/licenses/>.           ##
##                                                                            ##

### @controller controllers:IdeController ###
define ['routes','util/fonts'], (routes,fonts) -> ($scope, $location, $timeout, $routeParams, Dialog, Auth, Toasts, Session, Files) ->
  $scope.path =
    if $routeParams.path? and $routeParams isnt ''
      $routeParams.path.split('/')
    else []

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warning', 'You need to log in to view the requested resource!'
    return

  $scope.user = Auth.user

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

  $scope.fonts      = fonts
  $scope.editorFont = fonts.monospace[0]
  $scope.showLineNumbers = true
  $scope.editorFontSizeDefault = 12
  $scope.editorFontSize = $scope.editorFontSizeDefault

  $scope.chat = () ->
    Session.chat($scope.chatMessage)
    $scope.chatMessage = ""

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

  $scope.setFont = (font, where) ->
    $scope.editorFont = font

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

  # TODO: Move out
  $scope.date = (millis) -> new Date(millis)

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
      openOrClose = if $scope.session.me.activeFile is file.id
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

  slidebarActive = false
  previous = 0
  minheight = 24;
  height = minheight
  extendedHeight = 300

  $scope.showChat = false
  $scope.unreadChatMessages = 0

  setOutputResizing = (t) ->
    bar = document.getElementById('statusbar')
    ctn = document.getElementById('content')
    if t
      ctn.setAttribute 'class', 'resizing'
      bar.setAttribute 'class', 'resizing'
    else
      bar.removeAttribute 'class'
      ctn.removeAttribute 'class'

  setOutputHeight = (h) ->
    height = h
    bar = document.getElementById('statusbar')
    ctn = document.getElementById('content')
    ctn.style.bottom = height + 'px'
    bar.style.height = height + 'px'

  $scope.toggleChat = () ->
    if $scope.showChat
      setOutputHeight(minheight)
      $scope.showChat = false
    else
      $scope.unreadChatMessages = 0
      setOutputHeight(extendedHeight)
      $scope.showChat = true

  Session.info.talkback = (msg) ->
    unless $scope.showChat
      $scope.unreadChatMessages += 1
      Toasts.push 'info', "#{msg.s}: #{msg.m}"

  $scope.startSlidebar = ($event) ->
    slidebarActive = true
    previous = $event.clientY
    setOutputResizing(true)
    document.body.onmousemove = (e) ->
      height += previous - (previous = e.clientY)
      if height <= minheight
        height = minheight
        if $scope.showChat
          $timeout -> $scope.showChat = false
      else unless $scope.showChat
        $timeout ->
          $scope.unreadChatMessages = 0
          $scope.showChat = true
      setOutputHeight(height)
    document.body.onmouseup = document.body.onmouseleave = (e) ->
      setOutputResizing(false)
      slidebarActive = false
      if e.clientY > previous
        $timeout -> $scope.showChat = false
        setOutputHeight(minheight)
      else
        extendedHeight = height

      document.body.onmousemove = document.body.onmouseup = document.body.onmouseleave = undefined

  # TODO: This is very hacky and should be moved to a sidebar directive
  # in the future!
  $scope.select = (section) ->
    $scope.sidebar = true
    $scope.sidebarSection = section
    #top = $("#section-#{section}").position().top - 8
    #currentST = $('#sidebarContent').scrollTop()
    #$('#sidebarContent').animate
    #  scrollTop: currentST + top
