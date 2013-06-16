define ['angular', 'services/projects', 'services/files'], (angular,projects, files) ->
  module = angular.module 'clide.services', []
  module.service 'Projects', projects
  module.service 'Files', files