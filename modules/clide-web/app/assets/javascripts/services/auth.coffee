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

### @service services:Auth ###
### @require ngCookies from angular-cookies ###
define ['routes'], (routes) -> ($http, $cookies, $location) ->
  authentication = routes.clide.web.controllers.Authentication

  service = {
    user:
      username: localStorage['username']
      email: localStorage['email']
  }

  changeUser = (user) ->
    if user?
      localStorage['username'] = user.name
      localStorage['email'] = user.email
    else
      localStorage.removeItem 'username'
      localStorage.removeItem 'email'
    service.user.username = user?.username or null
    service.user.email = user?.email or null

  service.loggedIn = $cookies['PLAY_SESSION']?.indexOf("user") >= 0

  service.signup = (credentials,callbacks) ->
    $http.post(authentication.signup().url, credentials)
      .success (res) ->
        changeUser res
        callbacks.success?(res)
      .error (d...) -> callbacks.error?(d...)

  service.validateSession = (callbacks) ->
    $http.get(authentication.validateSession().url)
      .success (res) ->
        service.loggedIn = true
        changeUser res
        callbacks.success?(res)
      .error (e...) ->
        delete $cookies['PLAY_SESSION']
        service.loggedIn = false
        changeUser null
        callbacks.error?(e...)

  service.login = (credentials,callbacks) ->
    $http.post(authentication.login().url, credentials)
      .success (res) ->
        service.loggedIn = true
        changeUser res
        callbacks.success?(res)
      .error (d...) ->
        service.loggedIn = false
        callbacks.error?(d...)

  service.logout = (callbacks) ->
    $http.get(authentication.logout().url)
      .success ->
        service.loggedIn = false
        changeUser null
        callbacks.success?()
      .error (d...) ->
        callbacks.error?(d...)

  return service
