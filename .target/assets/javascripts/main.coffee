window.App = {}

require ['Router','views/Editor'], (Router,Editor) ->
  Typekit.load()

  window.App.router = new Router

  Backbone.history.start
    pushState: true

  editor = new Editor