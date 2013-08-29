### @service services:Projects ###
define ['routes'], (routes) -> ($q,$http) ->
  pc = routes.controllers.Projects

  get = (username) ->
    result = $q.defer()
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