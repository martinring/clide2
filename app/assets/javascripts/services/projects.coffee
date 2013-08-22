### @service services:Projects ###
define ['routes'], (routes) -> ($http) ->
  console.log 'initializing projects service'

  pc = routes.controllers.Projects

  cache = { }

  get = (username,success) ->
    unless cache[username]?
      update(username,success)
    else
      success(cache[username])

  update = (username, success) ->
    $http.get(pc.index(username).url)
      .success (res) ->
        console.log res
        cache[username] = res
        success(cache[username])  
      .error (d) -> console.log d


  return (
    get: get
    update: update
  )