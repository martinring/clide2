define ['../models/File','codemirror'], (File,Codemirror) ->
  class Editor extends Backbone.View
    tagName: 'div'
    initialize: () ->
      console.log Codemirror.version
      @model = new File unless @model?
      @