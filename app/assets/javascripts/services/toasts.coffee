### @service services:Toasts ###
define () -> ($rootScope) ->
  console.log 'initializing toast service'

  toasts = []

  config = 
    timeout: 5000

  push = (type, message) ->
    toast = 
      type: type
      message: message    
    toasts.push toast
    toast.remove = () -> 
      toasts.splice(toasts.indexOf(toast),1)
      if (!$rootScope.$$phase)
        $rootScope.$apply()
    toast.reset = () ->      
      toast.timeout = window.setTimeout(toast.remove, config.timeout) # TODO: move to settings
    toast.reset()
    if (!$rootScope.$$phase)
      $rootScope.$apply()    

  return (
    toasts: toasts
    config: config
    push: push
  )