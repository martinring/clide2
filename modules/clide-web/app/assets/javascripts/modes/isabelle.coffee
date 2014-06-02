##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  ##
##       | (__| | | (_| |  __/     http://clide.flatmap.net                   ##
##        \___|_|_|\__,_|\___|                                                ##
##                                                                            ##
##   This file is part of Clide.                                              ##
##                                                                            ##
##   Clide is free software: you can redistribute it and/or modify            ##
##   it under the terms of the GNU Lesser General Public License as           ##
##   published by the Free Software Foundation, either version 3 of           ##
##   the License, or (at your option) any later version.                      ##
##                                                                            ##
##   Clide is distributed in the hope that it will be useful,                 ##
##   but WITHOUT ANY WARRANTY; without even the implied warranty of           ##
##   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            ##
##   GNU General Public License for more details.                             ##
##                                                                            ##
##   You should have received a copy of the GNU Lesser General Public         ##
##   License along with Clide.                                                ##
##   If not, see <http://www.gnu.org/licenses/>.                              ##
##                                                                            ##

define ['modes/isabelle/defaultWords','codemirror'], (defaultWords) ->
  CodeMirror.defineMode "isabelle", (config,parserConfig) ->
    parserConfig = parserConfig or { }
    parserConfig.words = parserConfig.words or defaultWords

    # extracted from the isabelle reference manual
    greek       = "(?:\\\\<(?:alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|' +
      'mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|' +
      'Pi|Sigma|Upsilon|Phi|Psi|Omega)>)"
    digit       = "[0-9]"
    latin       = "[a-zA-Z]"
    sym         = "[\\!\\#\\$\\%\\&\\*\\+\\-\\/\\<\\=\\>\\?\\@\\^\\_\\|\\~]"
    letter      = "(?:#{latin}|\\\\<#{latin}{1,2}>|#{greek}|\\\\<\\^isu[bp]>)"
    quasiletter = "(?:#{letter}|#{digit}|\\_|\\')"
    ident       = "(?:#{letter}#{quasiletter}*)"
    longident   = "(?:#{ident}(?:\\.#{ident})+)"
    symident    = "(?:#{sym}+|\\\\<#{ident}>)"
    nat         = "(?:#{digit}+)"
    floating    = "(?:-?#{nat}\\.#{nat})"
    variable    = "(?:\\?#{ident}(?:\\.#{nat})?)"
    typefree    = "'#{ident}"
    typevar     = "\\?#{typefree}(?:\\.#{nat})"

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
    num         = /\#?-?[0-9]+(?:\.[0-9]+)?/
    escaped     = /\\[\"\\]/
    speciale    = /\\<[A-Za-z]+>/
    control     = /\\<\^[A-Za-z]+>/
    incomplete  = /\\<\^{0,1}[A-Za-z]*>?/
    lineComment = /--.*/

    tokenBase = (stream, state) ->
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
        return "control"
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
      if stream.match(escaped)
        return 'string'
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
      if stream.match(symident)
        return 'string symbol'
      if stream.match(control)
        return null
      if stream.match(incomplete)
        return 'string incomplete'
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

    return (
      startState: () ->
        string:        null
        tokenize:      tokenBase
        command:       null
        commentLevel:  0

      blockCommentStart: '(*'
      blockCommentEnd:   '*)'

      token: (stream,state) ->
        if stream.eatSpace()
          return null
        else
          return state.tokenize(stream, state)
    )

  CodeMirror.defineMIME("text/x-isabelle","isabelle")
