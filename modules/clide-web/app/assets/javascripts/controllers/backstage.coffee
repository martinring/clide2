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

### @controller clide.controllers:BackstageController ###
define ['util/md5'], (md5) -> ($scope, $location, $routeParams, $timeout, Projects, Console, Auth, Toasts, Dialog, BackstageSession) ->
  $scope.user = $routeParams.user

  unless Auth.loggedIn
    $location.path '/login'
    Toasts.push 'warning', 'You need to log in to view the requested resource!'
    return

  Auth.validateSession
    success: ->
      if $scope.user isnt Auth.user?.username
        $location.path '/login'
        Toasts.push 'warning', 'The requested resource is not associated with your user account!'
      else
        $scope.email = Auth.user.email
        $scope.gravatar = md5(Auth.user.email)
    error: ->
      $location.path '/login'
      Toasts.push 'warning', 'Sorry, your login session has expired! Please enter your credentials once again.'

  BackstageSession.init($scope.user)

  $scope.selectedProject = null

  $scope.Projects = BackstageSession.info

  $scope.selectProject = (project) ->
    $scope.selectedProject = project

  $scope.projectContextMenu = (project) ->
    [
      icon: 'trash'
      text: "delete '#{project.name}'"
      action: -> $scope.deleteProject(project)
    ]

  $scope.createProject = (name,description,error) -> Dialog.push
    error: error
    title: 'new project'
    queries: [
      { text: 'Name:', name: 'name', value: name }
      { text: 'Short description:', name: 'description', type: 'textarea', value: description }
    ]
    buttons: ['Ok','Cancel']
    done: (answer,result) -> if answer is 'Ok'
      Projects.put($scope.user,result)

  $scope.deleteProject = (project) -> Dialog.push
    title: "Delete project"
    text:  "Do you really want to delete project '#{project.name}'? " +
           "This can not be undone!"
    buttons: ['Yes','No']
    done: (answer) -> if answer is 'Yes'
      Projects.delete($scope.user,project)

  $scope.start = () ->
    $location.path "/#{$scope.selectedProject.owner}/#{$scope.selectedProject.name}/"
