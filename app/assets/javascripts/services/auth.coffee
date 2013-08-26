### @service services:Auth ###
### @import ngCookies from angular-cookies ###
define ['routes'], (routes) -> ($http, $cookies, $location) ->
  console.log 'initializing auth service'
  application = routes.controllers.Application  

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

  service.loggedIn = $cookies['PLAY_SESSION']?

  service.signup = (credentials,callbacks) ->
    $http.post(application.signup().url, credentials)
      .success (res) ->
        changeUser res
        callbacks.success?(res)
      .error (d...) -> callbacks.error?(d...)

  service.validateSession = (callbacks) ->
    $http.get(application.validateSession().url)
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
    $http.post(application.login().url, credentials)
      .success (res) ->
        service.loggedIn = true        
        changeUser res
        callbacks.success?(res)
      .error (d...) -> 
        service.loggedIn = false
        callbacks.error?(d...)

  service.logout = (callbacks) ->    
    $http.get(application.logout().url)
      .success ->
        service.loggedIn = false
        changeUser null
        callbacks.success?()
      .error (d...) ->
        callbacks.error?(d...)

  return service 