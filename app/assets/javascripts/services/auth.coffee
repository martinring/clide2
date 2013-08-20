### @service services:Auth ###
### @import ngCookies from angular-cookies ###
define ['routes'], (routes) -> ($http, $cookieStore) ->  
  console.log 'initializing auth service'
  application = routes.controllers.Application

  result = {
    user: $cookieStore.get('user') or null
  }

  $cookieStore.remove('user')

  changeUser = (user) ->
    result.user = user

  result.signup = (credentials,callbacks) ->
    $http.post(application.signup().url, credentials)
      .success (res) ->
        changeUser res        
        callbacks.success(res)
      .error callbacks.error  

  result.login = (credentials,callbacks) ->
    $http.post(application.login().url, credentials)
      .success (res) ->
        changeUser res        
        callbacks.success(res)
      .error callbacks.error

  result.logout = (callbacks) ->
    $http.post(application.logout().url)
      .success ->
        changeUser ''
        callbacks.success()
      .error callbacks.error      

  result