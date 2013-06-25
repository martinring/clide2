define ['angular', 'services/projects', 'services/files', 'services/app', 'services/console'], (angular, projects, files, app, console) ->
  module = angular.module 'clide.services', []  
  module.service 'Projects', projects
  module.service 'Files', files
  module.service 'App', app
  module.service 'Console', console  