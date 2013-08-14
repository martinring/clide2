define([
    'angular'
    'services/app'
    'services/auth'
    'services/console'
    'services/dialog' 
    'services/files'
    'services/projects'
    'services/toasts' 
  ], (angular, app, auth, console, dialog, files, projects, toasts) ->
    module = angular.module 'clide.services', []  
    module.service 'App', app
    module.service 'Auth', auth
    module.service 'Console', console  
    module.service 'Dialog', dialog
    module.service 'Files', files
    module.service 'Projects', projects
    module.service 'Toasts', toasts
  )