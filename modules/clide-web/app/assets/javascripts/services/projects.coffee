### @service services:Projects ###
define ['routes'], (routes) -> ($q,$http) ->
  pc = routes.clide.web.controllers.Projects

  get = (username, project) ->
    result = $q.defer()
    if project?
      $http.get(pc.details(username,project).url)
        .success(result.resolve)
        .error(result.reject)
    else
      $http.get(pc.index(username).url)
        .success(result.resolve)
        .error(result.reject)
    result.promise

  put = (username, project) ->
    result = $q.defer()
    $http.put(pc.put(username).url, project)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  del = (username, project) ->
    result = $q.defer()
    $http.delete(pc.delete(username, project.name).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

    

  return (
    get: get
    put: put
    delete: del    
  )