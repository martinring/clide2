define ->
  config =
    roles : [
      'public'
      'user'
      'admin'
    ]
    accessLevels:
      'public': "*"
      'anon': ['public']
      'user' : ['user', 'admin']
      'admin': ['admin']

  buildRoles = (roles) ->
    bitMask = "01"
    userRoles = {}
    for role in roles 
      intCode = parseInt(bitMask, 2)
      userRoles[roles[role]] =
        bitMask: intCode,
        title: roles[role]        
      bitMask = (intCode << 1 ).toString(2)    
    return userRoles    

  buildAccessLevels = (accessLevelDeclarations, userRoles) ->
    accessLevels = {}
    for level in accessLevelDeclarations
      decl = accessLevelDeclarations[level]        
      if typeof decl is 'string'
        if decl is '*'
          resultBitMask = ''
          for role in userRoles
            resultBitMask += '1'
          accessLevels[level] =
            bitMask: parseInt(resultBitMask,2)
            title: decl
        else console.log "Access Control Error: Could not parse '#{decl}' as access definition for level '#{level}'"
      else 
        resultBitMask = 0;
        for role in decl
          if userRoles.hasOwnProperty(decl[role])
            resultBitMask = resultBitMask | userRoles[decl[role]].bitMask
          else console.log "Access Control Error: Could not find role '#{decl[role]}' in registered roles while building access for '#{level}'"
        accessLevels[level] =
          bitMask: resultBitMask
          title:   decl[role]
    return accessLevels    
  
  userRoles = buildRoles(config.roles)

  return (
    userRoles: userRoles
    accessLevels: buildAccessLevels(config.accessLevels, userRoles)
  )