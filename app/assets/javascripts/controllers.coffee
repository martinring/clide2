define ['angular', 'controllers/app', 'controllers/ide','controllers/backstage','controllers/login','controllers/signup'], (angular, AppController, IdeController,BackstageController,LoginController,SignupController) ->
  module = angular.module 'clide.controllers', []
  module.controller 'AppController', AppController
  module.controller 'IdeController', IdeController
  module.controller 'BackstageController', BackstageController
  module.controller 'LoginController', LoginController
  module.controller 'SignupController', SignupController