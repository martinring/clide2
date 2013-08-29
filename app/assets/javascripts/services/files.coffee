### @service services:Files ###
define ['routes'], (routes) -> ($q,$http) ->
  fc = routes.controllers.Files

  get = (user,project) ->
    result = $q.defer()
    $http.get(fc.getTree(user,project).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  put = (user,project,path,name) ->    
    path = "" if path is "/"
    result = $q.defer()
    $http.put(fc.newFolder(user,project,path).url,name)
      .success(result.resolve)
      .error(result.resolve)
    result.promise

  return (
    get: get
    put: put
  )