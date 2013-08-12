define ['angular', 'services/projects', 'services/files', 'services/app', 'services/console', 'services/toasts', 'services/dialog'], (angular, projects, files, app, console, toasts, dialog) ->
  module = angular.module 'clide.services', []  
  module.service 'Projects', projects
  module.service 'Files', files
  module.service 'App', app
  module.service 'Console', console  
  module.service 'Toasts', toasts
  module.service 'Dialog', dialog
  