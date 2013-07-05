define () -> 
  (Projects) ->
    tree = [
      name: "foolder"
      type: 'dir'
      icon: '\uE156'
      collapsed: true
      files: [
        name: "foolder"
        type: 'dir'
        icon: '\uE156'
        collapsed: true
        files: [
            name: "baz"
            type: 'thy'
            opened: true
            icon: '\uE00F'
          ,
            name: "zap"
            type: 'thy'
            icon: '\uE00F'          
        ]
      ,
        name: "baz"
        type: 'thy'
        opened: true
        icon: '\uE00F'
      ,
        name: "zap"
        type: 'thy'
        icon: '\uE00F'          
    ,
      name: "foo"
      type: 'thy'
      icon: '\uE00F'
    ,
      name: "bar"
      type: 'thy'
      opened: true
      icon: '\uE00F'
    ,
      name: "baz"
      type: 'thy'
      opened: true
      icon: '\uE00F'  
      ] 
    ]
    return (  
      files: tree
    )