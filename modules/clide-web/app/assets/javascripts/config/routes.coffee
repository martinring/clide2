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

### @config ###
define ['routes'], (routes) -> ($routeProvider, $locationProvider) ->
  $locationProvider.html5Mode(true)

  $routeProvider.when '/'
    redirectTo: '/login'
  $routeProvider.when '/login'
    title:       'login'
    templateUrl: '/client/partials/login.html'
    controller:  'LoginController'
  $routeProvider.when '/signup'
    title:       'signup'
    templateUrl: '/client/partials/signup.html'
    controller:  'SignupController'
  $routeProvider.when '/admin'
    title:       'admin'
    templateUrl: '/client/partials/admin.html'
    controller:  'AdminController'
  $routeProvider.when '/:user/backstage'
    title:       'backstage'
    templateUrl: '/client/partials/backstage.html'
    controller:  'BackstageController'
  $routeProvider.when '/:user/:project',
    title:       'coding'
    ide:         true
    templateUrl: '/client/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.when '/:user/:project/:path*',
    title:       'coding'
    ide:         true
    templateUrl: '/client/partials/ide.html'
    controller:  'IdeController'
  $routeProvider.when '/404',
    title:       'not found'
    templateUrl: '/client/partials/404.html'
  $routeProvider.when '/401',
    title:       'not authorized'
    templateUrl: '/client/partials/401.html'
  $routeProvider.otherwise
    redirectTo: '/404'
