CodeMirror.defineMode "isabelle", (config,parserConfig) ->  
  # extracted from the isabelle reference manual
  greek       = "(?:\\\\<(?:alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|' +
    'mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|' +
    'Pi|Sigma|Upsilon|Phi|Psi|Omega)>)"
  digit       = "[0-9]"
  latin       = "[a-zA-Z]"
  sym         = "[\\!|\\#|\\$|\\%|\\&|\\*|\\+|\\-|\\/|\\<|\\=|\\>|\\?|\\@|\\^|\\_|\\||\\~]"
  letter      = "(?:#{latin}|\\\\<#{latin}{1,2}>|#{greek}|\\\\<^isu[bp]>)"
  quasiletter = "(?:#{letter}|#{digit}|\\_|\\')"
  ident       = "(?:#{letter}#{quasiletter}*)"
  longident   = "(?:#{ident}(?:\\.#{ident})+)"
  symident    = "(?:#{sym}+|\\\\<#{ident}>)"
  nat         = "(?:#{digit}+)"
  floating    = "-?#{nat}\\.#{nat}"  
  variable    = "\\?#{ident}(?:\\.#{nat})?"
  typefree    = "'#{ident}"
  typevar     = "\\?#{typefree}(?:\\.#{nat})"
  string      = "\\\".*\\\""
  altstring   = "`.*`"
  verbatim    = "{\\*.*\\*}"  
  abbrev =
    '\\<\\.|\\.\\>|\\(\\||\\|\\)|\\[\\||\\|\\]|\\{\\.|\\.\\}|\\/\\\\|\\\\\\/' +
    '|\\~\\:|\\(\\=|\\=\\)|\\[\\=|\\=\\]|\\+o|\\+O|\\*o|\\*O|\\.o|\\.O' +
    '|\\-o|\\/o|\\=\\_\\(|\\=\\_\\)|\\=\\^\\(|\\=\\^\\)|\\-\\.|\\.\\.\\.|(?:Int|Inter' +
    "|Un|Union|SUM|PROD)(?!#{quasiletter})"  

  abbrev      = RegExp abbrev
  greek       = RegExp greek      
  digit       = RegExp digit      
  latin       = RegExp latin      
  sym         = RegExp sym        
  letter      = RegExp letter     
  quasiletter = RegExp quasiletter
  ident       = RegExp ident      
  longident   = RegExp longident  
  symident    = RegExp symident   
  nat         = RegExp nat        
  floating    = RegExp floating   
  variable    = RegExp variable   
  typefree    = RegExp typefree   
  typevar     = RegExp typevar    
  string      = RegExp string     
  altstring   = RegExp altstring  
  verbatim    = RegExp verbatim   
  num         = /\#?-?[0-9]+(?:\.[0-9]+)?/
  escaped     = /\\[\"\\]/
  speciale    = /\\<[A-Za-z]+>/
  control     = /\\<\^[A-Za-z]+>/
  incomplete  = /\\<\^{0,1}[A-Za-z]*>?/
  lineComment = /--.*/
  conj        = /\/\\/
  disj        = /\\\//

  special = 
    startState: () ->
      control: null
      sub:     false
      sup:     false
    token: (stream,state) ->
      if stream.sol()
        state.control = null
      x = ''
      if      state.sub then x = 'sub control-sub '
      else if state.sup then x = 'sup control-sup '
      if state.control is 'sub'        
        stream.match(incomplete) or stream.next()
        state.control = null
        return x + 'sub'
      if state.control is 'sup'
        stream.match(incomplete) or stream.next()
        state.control = null
        return x + 'sup'
      if state.control is 'bold'
        console.log 'insub'
        stream.match(incomplete) or stream.next()
        state.control = null
        return x + 'bold'    
      if stream.eatWhile(/[^\\]/)
        if stream.match(speciale,false) or stream.match(control,false)
          if x isnt ''
            return x
          else
            return null        
        else
          until stream.eol() or stream.match(speciale,false) or stream.match(control,false)
            stream.next()
            stream.eatWhile(/[^\\]/)
      if stream.match(/\\<\^[A-Za-z]+>/)
        switch stream.current()
          when '\\<^sub>'            
            state.control = 'sub'            
          when '\\<^sup>'
            state.control = 'sup'
          when '\\<^isub>'
            state.control = 'sub'
          when '\\<^isup>'
            state.control = 'sup'
          when '\\<^bold>'
            state.control = 'bold'
          when '\\<^bsub>'
            state.sub = true
            return "#{x}control control-sub"
          when '\\<^bsup>'
            state.sup = true
            return "#{x}control control-sup"
          when '\\<^esub>'
            state.sub = false
            return "control"
          when '\\<^esup>'
            state.sup = false
            return "control"
        if state.control?
          return "#{x}control control-#{state.control}"
        else
          return x + 'control'
      if stream.match(/\\<[A-Za-z]+>/)
        return x + 'special'      
      if x isnt ''
        return x
      return null

  tokenBase = (stream, state) ->    
    #if stream.match(lineComment)
    #  return "comment"
      
    ch = stream.peek()    

    # verbatim
    if ch is '{'
      stream.next()
      if stream.eat('*')        
        state.verbatimLevel++
        state.tokenize = tokenVerbatim
        return state.tokenize(stream, state)
      else stream.backUp(1)
    
    state.command = null

    # string
    if ch is '"'
      stream.next()
      state.tokenize = tokenString
      return "string"

    # alt string
    if ch is '`'
      stream.next()
      state.tokenize = tokenAltString
      return "altstring"

    # comment
    if ch is '('
      stream.next()
      if stream.eat('*')
        state.commentLevel++
        state.tokenize = tokenComment
        return state.tokenize(stream, state)   
      else stream.backUp(1)   

    if stream.match(abbrev)      
      return 'symbol'
    if stream.match(typefree)
      return 'tfree'
    else if stream.match(typevar)
      return "tvar"    
    else if stream.match(variable)
      return "var"    
    else if stream.match(longident) or stream.match(ident)
      type = parserConfig.words[stream.current()] || "identifier"
      if type is 'command'        
        type = type + " " + stream.current()
        state.command = stream.current()
      return type
    else if stream.match(symident)      
      return "symbol"
    else if stream.match(control)
      return null
    else if stream.match(incomplete)
      return 'incomplete'

    stream.next()
    return null

  tokenString = (stream, state) ->
    if stream.eatSpace()
      return 'string'
    if stream.match('\"')
      state.tokenize = tokenBase
      return 'string'
    if stream.match(abbrev)
      return 'string symbol'    
    if stream.match(longident)
      return 'string longident'
    if stream.match(ident)
      return 'string ident'
    if stream.match(typefree)
      return 'string tfree'
    if stream.match(typevar)
      return 'string tvar'    
    if stream.match(num)
      return 'string num'
    if stream.match(escaped)
      return 'string'    
    if stream.match(symident)
      return 'string symbol'
    if stream.match(control)
      return null
    else if stream.match(incomplete)
      return 'incomplete'
    stream.next()
    return 'string'

  tokenAltString = (stream, state) ->
    next = false
    end = false
    escaped = false
    while ((next = stream.next())?)
      if next is '`' and not escaped
        end = true
        break 
      escaped = not escaped and next is '\\'    
    if end and not escaped
      state.tokenize = tokenBase    
    return 'alt_string'  

  tokenComment = (stream, state) ->
    prev = null
    next = null
    while state.commentLevel > 0 and (next = stream.next())?
      if prev is '(' and next is '*' then state.commentLevel++
      if prev is '*' and next is ')' then state.commentLevel--
      prev = next    
    if state.commentLevel <= 0
      state.tokenize = tokenBase    
    return 'comment'

  tokenVerbatim = (stream, state) ->
    prev = null
    next = null
    while (next = stream.next())?      
      if prev is '*' and next is '}'
        state.tokenize = tokenBase
        return 'verbatim' + (if state.command? then ' ' + state.command else '')
      prev = next
    return 'verbatim' + (if state.command? then ' ' + state.command else '')

  CodeMirror.overlayMode((
    startState: () ->
      string:        null
      tokenize:      tokenBase
      command:       null
      commentLevel:  0

    token: (stream,state) ->
      if stream.sol() and stream.match(/(?:[ \t]*\|[ \t]*)|(?:[ \t]+)/)
        return "indent"
      if stream.eatSpace()
        return null
      else
        return state.tokenize(stream, state)
  ),special,true)

CodeMirror.defineMIME("text/x-isabelle","isabelle")