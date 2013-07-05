define () -> () ->
  class Console 
    lines: []
    write: (line,type='info') =>
      @lines.push
        text: line
        type: type    

  return new Console