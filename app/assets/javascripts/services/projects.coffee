### @service services:Projects ###
define ['routes'], (routes) -> ($http,$timeout) ->
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
        cache[username] = res
        success(cache[username])  
      .error (d) -> console.log d

  create = (username, project, callbacks) ->    
    $http.put(pc.create(username).url, project)
      .success (project) -> 
        get username, (ps) ->
          ps.push project
          callbacks.success()
      .error (e) ->
        callbacks.error(e)

  return (
    get: get
    update: update
    create: create
  )