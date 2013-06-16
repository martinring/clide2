define ['angular', 'controllers/app','controllers/project'], (angular, AppController,ProjectController) ->
  module = angular.module 'clide.controllers', []
  module.controller 'AppController', AppController()
  module.controller 'ProjectController', ProjectController()  