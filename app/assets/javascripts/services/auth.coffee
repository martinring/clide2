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

  console.log $cookies
  service.loggedIn = $cookies['PLAY_SESSION']?

  console.log $cookies.PLAY_SESSION

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