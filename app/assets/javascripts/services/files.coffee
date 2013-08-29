### @service services:Files ###
define ['routes'], (routes) -> ($q,$http) ->
  pc = routes.controllers.Project

  get = (user,project) ->
    result = $q.defer()
    $http.get(pc.fileTree(user,project).url)
      .success(result.resolve)
      .error(result.reject)
    result.promise

  return (
    get: get
  )