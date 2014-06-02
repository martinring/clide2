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

### @service services:Toasts ###
define () -> ($rootScope,$timeout) ->
  toasts = []

  config =
    timeout: 250

  push = (type, message) ->
    toast =
      type: type
      message: message
      life: 100
    toasts.push toast
    toast.remove = () ->
      toasts.splice(toasts.indexOf(toast),1)
    toast.refresh = () ->
      toast.life = 100
    toast.decease = () ->
      if toast.life > 0
        toast.life -= 5
        $timeout(toast.decease, config.timeout)
      else
        toast.remove()
    toast.reset = () ->
      $timeout(toast.decease, config.timeout) # TODO: move to settings
    toast.reset()
    if (!$rootScope.$$phase)
      $rootScope.$apply()

  return (
    toasts: toasts
    config: config
    push: push
  )
