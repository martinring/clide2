### @service services:Toasts ###
define () -> ($rootScope,$timeout) ->
  toasts = []

  config = 
    timeout: 250

  push = (type, message) ->
    toast = 
      type: type
      message: message
      life: 100
    toasts.push toast
    toast.remove = () -> 
      toasts.splice(toasts.indexOf(toast),1)      
    toast.refresh = () -> 
      toast.life = 100
    toast.decease = () ->
      if toast.life > 0
        toast.life -= 5
        $timeout(toast.decease, config.timeout)
      else
        toast.remove()      
    toast.reset = () ->
      $timeout(toast.decease, config.timeout) # TODO: move to settings
    toast.reset()
    if (!$rootScope.$$phase)
      $rootScope.$apply()

  return (
    toasts: toasts
    config: config
    push: push
  )