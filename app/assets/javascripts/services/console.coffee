define () -> () ->
  class Console 
    lines: []
    write: (line) =>
      @lines.push(line)

  return new Console