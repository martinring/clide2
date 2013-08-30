### @service services:Files ###
define ['routes'], (routes) -> ($q,$http) ->
  fc = routes.controllers.Files

  get = (user,project) ->
    result = $q.defer()
    $http.get(fc.getTree(user,project).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  put = (user,project,path,file) ->        
    result = $q.defer()
    $http.put(fc.newFile(user,project,path).url,file)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  del = (user,project,path) ->
    result = $q.defer()
    $http.delete(fc.deleteFile(user,project,path).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  return (
    get: get
    put: put
    delete: del
  )