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

### @controller controllers:SignupController ###
define ['routes','util/md5'], (routes,md5) -> ($scope, $location, Console, Toasts, Auth) ->
  $scope.gravatar = null
  $scope.data =
    username: null
    email: null
    password: null
  $scope.updateGravatar = () -> if $scope.data.email?
    $scope.gravatar = md5($scope.data.email)
  $scope.signup = () ->
    $scope.error = { }
    Console.write "signing up as '#{$scope.username}'..."
    Auth.signup $scope.data,
      success: ->
        $location.path "/login"
        Toasts.push('success',"Welcome, your account has been created! :)")
      error: (data,status) ->
        switch status
          when 400
            $scope.error = data
          when 404
            $scope.error[''] = 'the server did not respond'
          else
            $scope.error[''] = 'something went wrong...'

