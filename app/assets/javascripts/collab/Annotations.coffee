define ['collab/Operation'], (Operation) ->
  class Annotations
    constructor: () ->
      @current = [[14,25,'hallo'],[15,23,'hallo']]
      @buffered = ""

    transform: (op) ->      
      result = []
      position = 0
      index = 0
      for a in op.actions
        console.log (Operation.actionType a)
        switch Operation.actionType a
          when 'retain'            
            position += a
            from = index
            while @current[index]?[0] < position
              index += 1
            range = @current[from...index]
            result.push(range...)
          when 'insert'            
            while @current[index]?[0] >= position and @current[index][1] < position + a.length              
              @current[index][2] += a.length
              result.push @current[index]
              index += 1
          when 'delete'
            dindex = index
            while @current[dindex]?[0] >= position and @current[dindex][1] < position - a
              if @current[dindex][1] - position > (-a)
                @current[dindex][2] += a
              else if @current[dindex][1] - position <= -a
                @current[dindex][2] = position
              unless @current[dindex][1] > @current[dindex][2]
                result.push @current[dindex]
              dindex += 1              
            position -= a
      @current = result