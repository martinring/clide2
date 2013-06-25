define () -> (Projects) ->
  files: [
      name: "#{Projects.current}-file1"
      type: 'thy'
    ,
      name: "#{Projects.current}-file1"
      type: 'thy'
    ,
      name: "#{Projects.current}-folder1"
      type: 'dir'
      files: [
          name: "#{Projects.current}-file1"
          type: 'thy'
        ,
          name: "#{Projects.current}-file1"
          type: 'thy'
        ]
    ]
  openFiles: [
      name: "blubb"
      type: 'thy' 
    ,
      name: "flubb"
      type: 'thy'   
  ]