define ['util/checkFont'], (checkFont) ->  
  monospace = [
    'Inconsolata'
    'Consolas'    
    'DejaVu Sans Mono'
    'Monaco'
    'Ubuntu Mono'
    'Bitstream Vera Sans Mono'    
    'Courier New'    
    'Droid Sans Mono'    
    'Latin Modern Mono'
    'Lucida Console'
    'Menlo'    
  ]

  math = [
    'Computer Modern'
    'Cambria Math'
  ]

  return (
    monospace: monospace.filter(checkFont)
    math:      math.filter(checkFont)
  )