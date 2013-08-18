### @service services:Console ###
define () -> () ->
  console.log 'initializing console service'
  
  class Console 
    lines: []
    write: (line,type='info') =>
      @lines.push
        text: line
        type: type      

  return new Console