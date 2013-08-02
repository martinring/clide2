define ['angular', 'controllers/app', 'controllers/ide','controllers/backstage','controllers/login','controllers/signup', 'controllers/collab'], (angular, AppController, IdeController,BackstageController,LoginController,SignupController,CollabController) ->
  module = angular.module 'clide.controllers', []
  module.controller 'AppController', AppController
  module.controller 'IdeController', IdeController
  module.controller 'BackstageController', BackstageController
  module.controller 'LoginController', LoginController
  module.controller 'SignupController', SignupController
  module.controller 'CollabController', CollabController