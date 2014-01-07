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

### @service services:BackstageSession ###
define ['routes','util/actorSocket'], (routes,ActorSocket) -> ($q,$rootScope,$http,Toasts) ->
  (username) ->
    url = routes.clide.web.controllers.Projects.backstageSession(username).webSocketURL()

    session =
      state: 'closed'
      projects: null
      otherProjects: null

    apply = (f) -> unless $rootScope.$$phase then $rootScope.$apply(f)

    new ActorSocket url, "#{username}/backstage", (context) ->
      data: session
      preStart: ->
        context.setReceiveTimeout 500
        context.tellAck { t: 'init' }
      receive: (msg) -> switch msg.t
        when 'timeout'
          context.log.warn 'retrying init'
          context.restart()
        when 'projects'
          context.setReceiveTimeout null
          apply ->
            session.projects = msg.c.own
            session.otherProjects = msg.c.other
        when 'access'
          apply ->
            session.otherProjects = session.otherProjects.filter((p) -> p.id isnt msg.c.p.id)
            if msg.c.l > 0
              session.otherProjects.push(msg.c.p)
        when 'createdproject'
          apply ->
            if msg.c.owner is username
              session.projects.push(msg.c)
            else
              session.otherProjects.push(msg.c)
        when 'deletedproject'
          apply ->
            session.projects = session.projects.filter((p) -> p.id isnt msg.c)
            session.otherProjects = session.otherProjects.filter((p) -> p.id isnt msg.c)
