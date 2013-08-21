### @service services:Auth ###
### @import ngCookies from angular-cookies ###
define ['routes'], (routes) -> ($http, $cookieStore) ->
  console.log 'initializing auth service'
  application = routes.controllers.Application

  service = {
    user: $cookieStore.get('user') or null
  }

  $cookieStore.remove('user')

  changeUser = (user) ->
    service.user = user

  service.signup = (credentials,callbacks) ->
    $http.post(application.signup().url, credentials)
      .success (res) ->
        changeUser credentials
        callbacks.success(res)
      .error callbacks.error

  service.login = (credentials,callbacks) ->
    $http.post(application.login().url, credentials)
      .success (res) ->
        changeUser credentials
        callbacks.success(res)
      .error callbacks.error

  service.logout = (callbacks) ->
    $http.post(application.logout().url)
      .success ->
        changeUser null
        callbacks.success()
      .error callbacks.error

  service