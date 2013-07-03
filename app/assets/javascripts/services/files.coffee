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
            icon: '\uE0EF'
          ,
            name: "zap"
            type: 'thy'
            icon: '\uE0EF'          
        ]
      ,
        name: "baz"
        type: 'thy'
        opened: true
        icon: '\uE0EF'
      ,
        name: "zap"
        type: 'thy'
        icon: '\uE0EF'          
    ,
      name: "foo"
      type: 'thy'
      icon: '\uE0EF'
    ,
      name: "bar"
      type: 'thy'
      opened: true
      icon: '\uE0EF'
    ,
      name: "baz"
      type: 'thy'
      opened: true
      icon: '\uE0EF'  
      ] 
    ]
    return (  
      files: tree
    )