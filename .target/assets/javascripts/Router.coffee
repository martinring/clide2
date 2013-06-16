define () ->
  class Router extends Backbone.Router
    routes:
        ""           : "project"
        ":node"      : "node"
        ":node/:pos" : "node"