### @service services:Auth ###
### @import ngCookies from angular-cookies ###
define ['routes'], (routes) -> ($http, $cookieStore, $location) ->
  console.log 'initializing auth service'
  application = routes.controllers.Application  

  service = {
    user:
      session: localStorage['session']
      username: localStorage['username']
      email: localStorage['email']
  }


  changeUser = (user) ->    
    if user?
      localStorage['session'] = user.session
      localStorage['username'] = user.name
      localStorage['email'] = user.email
    else
      localStorage.removeItem 'session'
      localStorage.removeItem 'username'
      localStorage.removeItem 'email'
    service.user.session = user?.session or null
    service.user.username = user?.username or null
    service.user.email = user?.email or null

  service.loggedIn = () -> service.user.session?

  service.signup = (credentials,callbacks) ->
    $http.post(application.signup().url, credentials)
      .success (res) ->                
        changeUser res
        callbacks.success?(res)
      .error (d) -> callbacks.error?(d)

  service.validateSession = (callbacks) ->
    $http.post(application.validateSession().url, service.user)
      .success (res) ->
        console.log 'user validated'
        changeUser res
        callbacks.success?(res)
      .error (e) ->            
        console.log 'validation failed'
        changeUser null
        callbacks.error?(e)

  service.login = (credentials,callbacks) ->
    $http.post(application.login().url, credentials)
      .success (res) ->
        changeUser res
        callbacks.success?(res)
      .error (d) -> callbacks.error?(d)

  service.logout = (callbacks) ->
    changeUser null
    callbacks.success?()
    #$http.post(application.logout().url)
    #  .success ->
    #    changeUser null
    #    callbacks.success()
    #  .error callbacks.error  

  return service 