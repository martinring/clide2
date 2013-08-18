### @service services:App ###
define () -> ($rootScope) ->  

  class App 
    user: undefined
    wait: false
    waitWhile: (f) ->
      wait = true
      f()
      wait = false
  
  return new App