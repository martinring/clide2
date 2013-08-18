### @service services:Auth ###
### @import ngCookies from angular-cookies ###
define ['underscore', 'routes', 'config/access/roles'], (_,routes,roles) -> ($http, $cookieStore) ->
  console.log 'initializing auth service'

  accessLevels = roles.accessLevels
  userRoles = roles.userRoles

  currentUser = $cookieStore.get('user') or { 
    username: ""
    role: userRoles['public']
  }

  $cookieStore.remove('user')

  changeUser = (user) ->
    _.extend(currentUser,user)
  
  return (
    authorize: (accessLevel, role) ->
      if role is undefined
        role = currentUser.role
      return accessLevel.bitMask & role.bitMask

    isLoggedIn: (user) ->
      if (user is undefined)
        user = currentUser
      return user.role.title is userRoles.user.title or 
             user.role.title is userRoles.admin.title

    signup: (user,success,error) ->
      routes.controllers.Application.signup().ajax
        data: user
        success: success
        error: error

    login: (user,success,error) ->      
      routes.controllers.Application.login().ajax
        data: user
        success: success
        error: error

    logout: (success, error) ->
      routes.controllers.Application.logout().ajax
        success: success
        errror: error

    accessLevels: accessLevels

    userRoles: userRoles

    user: currentUser
  )