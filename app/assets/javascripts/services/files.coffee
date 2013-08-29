### @service services:Files ###
define ['routes'], (routes) -> ($q,$http) ->
  fc = routes.controllers.Files

  get = (id) ->
    result = $q.defer()
    $http.get(fc.getFiles(id).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  put = (folder,name) ->
    result = $q.defer()
    $http.put(fc.newFolder(folder.id,name).url)
      .success(result.resolve)
      .error(result.resolve)
    result.promise

  return (
    get: get
    put: put
  )