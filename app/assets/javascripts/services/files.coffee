### @service services:Files ###
define () -> (Projects) -> 
  tree = [
    name: "foolder"
    type: 'dir'
    icon: 'icon-angle-right'
    collapsed: true
    files: [
      name: "foolder"
      type: 'dir'
      icon: 'icon-angle-right'
      files: [
          name: "baz"
          type: 'thy'          
          icon: 'icon-file-alt'
        ,
          name: "zap"
          type: 'thy'
          icon: 'icon-file-alt'          
      ]
    ,
      name: "baz"
      type: 'thy'      
      icon: 'icon-file-alt'
    ,
      name: "zap"
      type: 'thy'
      icon: 'icon-file-alt'          
  ,
    name: "foo"
    type: 'thy'
    icon: 'icon-file-alt'
  ,
    name: "bar"
    type: 'thy'    
    icon: 'icon-file-alt'
  ,
    name: "baz"
    type: 'thy'    
    icon: 'icon-file-alt'  
    ] 
  ]

  return (
    root: 
      name: "__ROOT"
      files: tree
  )