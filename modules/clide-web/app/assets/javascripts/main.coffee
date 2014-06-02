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

# RequireJS configuration
require.config
  paths:
    'codemirror':         'vendor/codemirror/codemirror-compressed'
  shim:
    'codemirror':
      exports: 'CodeMirror'
    'routes':
      exports: 'jsRoutes'


require ['app'], (app) ->
  app.run ($rootScope, Session, Files) ->
    $rootScope.$on '$routeChangeSuccess', (e,n,o) ->
      $rootScope.title = n.$$route.title
      #unless n.$$route.ide
      #  # TODO !!!
      #  #iles.close()
      #  #ession.close()

  angular.element(document).ready ->
    angular.bootstrap document, ['clide-web']
    angular.element(document.getElementById('loading')).remove()
