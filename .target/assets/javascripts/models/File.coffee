define () ->
  class File extends Backbone.Model
    defaults: 
      path: undefined
      name: undefined
      version: 0