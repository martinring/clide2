##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU Lesser General Public License as           ##
##   published by the Free Software Foundation, either version 3 of           ##
##   the License, or (at your option) any later version.                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU Lesser General Public         ##
##   License along with Clide.                                                ##
##   If not, see <http://www.gnu.org/licenses/>.                              ##
##                                                                            ##

### @controller controllers:IdeController ###
define ['routes','util/fonts'], (routes,fonts) -> ($scope, $location, $timeout, $routeParams, $sce, Dialog, Auth, Toasts, Session, Files) ->
  $scope.path =
    if $routeParams.path? and $routeParams isnt ''
      $routeParams.path.split('/')
    else []

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warning', 'You need to log in to view the requested resource!'
    return

  $scope.user = Auth.user

  ## init fileBrowser ------------------------------------------------------- ##

  fileBrowserService = null
  fileService = null

  $scope.reconnect = ->
    fileBrowserService = Files $routeParams.user, $routeParams.project, $scope.path
    fileService = fileBrowserService.interface
    $scope.fileService = fileBrowserService
    $scope.files = fileBrowserService.data
    $scope.browseTo = fileService.browseTo

  $scope.reconnect()

  ## init collab session ---------------------------------------------------- ##

  sessionService = null
  session = null

  $scope.reconnectSession = ->
    openFiles = []
    sessionService = Session $routeParams.user, $routeParams.project
    session = sessionService.interface
    $scope.session = sessionService.data
    $scope.sessionService = sessionService
    console.log sessionService.state
    sessionService.data.kicked = () ->
      Toasts.push 'warning', "You have been kicked from '#{$routeParams.user}/#{$routeParams.project}'"
      $scope.backstage()
    sessionService.data.talkback = (msg) ->
      unless $scope.showChat
        $scope.unreadChatMessages += 1
        Toasts.push 'info', "#{msg.s.user}: #{msg.m}"

  $scope.reconnectSession()

  ## ------------------------------------------------------------------------ ##

  $scope.subscribe = (file, user, name) -> session.subscribe(file,user,name)
  $scope.unsubscribe = (file, user, name) -> session.unsubscribe(file,user,name)

  $scope.$on '$destroy', ->
    fileBrowserService?.stop()
    sessionService?.stop()

  $scope.backstage = () ->
    $location.path "/#{Auth.user.username}/backstage"

  $scope.start = () ->
    $scope.state = 'ide'

  $scope.fonts      = fonts
  $scope.editorFont = fonts.monospace[0]
  $scope.showLineNumbers = true
  $scope.editorFontSizeDefault = 12
  $scope.editorFontSize = $scope.editorFontSizeDefault


  $scope.chatMessage = ''
  $scope.chat = (msg) ->
    console.log msg
    if msg? and msg isnt ''
      session.chat(msg)

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
        session.invite(result.username)

  $scope.openFile = (file) ->
    if file.isDirectory
      file.loading = true
      $scope.browseTo(file.path, file.id)
    else
      session.openFile(file.id or file)

  $scope.setColor = (color) ->
    session.setColor(color)

  $scope.setFont = (font, where) ->
    $scope.editorFont = font

  $scope.closeFile = (id) ->
    session.closeFile(id)

  $scope.deleteFile = (file) ->
    if file.isDirectory
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete the folder '#{file.path[file.path.length - 1]}' and all of its content? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          fileService.delete(file.path)
    else
      Dialog.push
        title: "delete '#{file.name}'"
        text: "Do you really want to delete '#{file.path[file.path.length - 1]}'? This can not be undone!"
        buttons: ['Yes','No']
        done: (answer) -> if (answer is 'Yes')
          fileService.delete(file.path)

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
          fileService.touchFile(p)
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
          fileService.touchFolder(p)
        else
          result.error = 'Please enter a name'

  $scope.userContextMenu = (user) ->
    un_follow = if user.followed
      icon: 'eye'
      text: 'unfollow activity'
      action: -> $scope.unfollowUser(user)
    else
      icon: 'eye'
      text: 'follow activity'
      action: -> $scope.followUser(user)
    [
      un_follow
    ,
      icon: 'hand-o-right'
      text: "Kick #{user.user}"
      action: -> $scope.kickUser(user)
    ]

  $scope.kickUser = (user) ->
    session.kick(user.id)

  $scope.followUser = (user) ->
    session.follow(user.id)

  $scope.fileContextMenu = (file) ->
    if (file.isDirectory)
      file.expand = true
      [
        icon: 'folder-open'
        text: 'Open'
        action: -> $scope.openFile(file)
      ,
        icon: 'trash-o'
        text: 'Delete'
        action: -> $scope.deleteFile(file)
      ]
    else
      openOrClose = if $scope.session.me.activeFile is file.id
          icon: 'times'
          text: 'Close'
          action: -> $scope.closeFile(file.id)
        else
          icon: 'edit'
          text: 'Edit'
          action: -> $scope.openFile(file)
      [ openOrClose,
        icon: 'trash-o'
        text: 'Delete'
        action: -> $scope.deleteFile(file)
      ]

  slidebarActive = false
  previous = 0
  minheight = 24;
  height = minheight
  extendedHeight = 300

  $scope.showChat = false
  $scope.showOutput = false
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
    else if $scope.showOutput
      $scope.showOutput = false
      $scope.showChat = true
    else
      $scope.unreadChatMessages = 0
      setOutputHeight(extendedHeight)
      $scope.showChat = true

  $scope.toggleOutput = () ->
    if $scope.showOutput
      setOutputHeight(minheight)
      $scope.showOutput = false
    else if $scope.showChat
      $scope.showOutput = true
      $scope.showChat = false
    else
      $scope.unreadChatMessages = 0
      setOutputHeight(extendedHeight)
      $scope.showOutput = true

  $scope.startSlidebar = ($event) ->
    slidebarActive = true
    previous = $event.clientY
    setOutputResizing(true)
    document.body.onmousemove = (e) ->
      height += previous - (previous = e.clientY)
      if height <= minheight
        height = minheight
        if $scope.showChat or $scope.showOutput
          $timeout ->
            $scope.showChat = false
            $scope.showOutput = false
      else unless $scope.showChat or $scope.showOutput
        $timeout ->
          $scope.unreadChatMessages = 0
          $scope.showChat = true
      setOutputHeight(height)
    document.body.onmouseup = document.body.onmouseleave = (e) ->
      setOutputResizing(false)
      slidebarActive = false
      if e.clientY > previous
        $timeout ->
          $scope.showChat = false
          $scope.showOutput = false
        setOutputHeight(minheight)
      else
        extendedHeight = height

      document.body.onmousemove = document.body.onmouseup = document.body.onmouseleave = undefined

  # TODO: This is very hacky and should be moved to a sidebar directive
  # in the future!
  $scope.select = (section) ->
    $scope.sidebar = true
    $scope.sidebarSection = section
    top = $("#section-#{section}").position().top - 16
    $('#sidebarContent').animate(
      { scrollTop: $("#section-#{section}").offset.top },
      2000)

  $scope.detachOutput = () ->
    popup = window.open('about:blank','_blank','height=400, width=600, resizable=no, toolbar=no, scrollbars=no, menubar=no, status=no, directories=no')
    popup.document.write('<html><head><title>Output</title>')
    popup.document.write(document.getElementById('theme').outerHTML)
    popup.document.write('</head><body>')
    popup.document.write($('#output-content').html())
    popup.document.write('</body></html>')

  $scope.trustedHtml = (code) -> $sce.trustAsHtml(code)
