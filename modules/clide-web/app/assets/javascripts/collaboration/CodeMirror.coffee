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

## Loosely Based on the javascript ot implementation 'ot.js' by Tim Baumann (MIT
## License) see https://github.com/Operational-Transformation/ot.js

define ['collaboration/Operation','collaboration/Annotations','codemirror'], (Operation,Annotations,CodeMirror) ->
  CodeMirror.commands.getHelp = (cm) ->
    doc = cm.getDoc()
    if doc? and !doc.somethingSelected()
      CodeMirror.signal(doc,'getHelp',doc,doc.indexFromPos(doc.getCursor()))
  CodeMirror.keyMap['default']['Ctrl-Space'] = 'getHelp'

  class CodeMirrorAdapter
    constructor: (@doc,@color) ->
      @doc.on "beforeChange", @onChange
      @doc.on "cursorActivity", @onSelectionChange
      @doc.on "getHelp", @onGetHelp

      @annotations = {}
      @autocompletes = {}

    setColor: (color) =>
      @color = color
      @doc.setSelection(@doc.getCursor('anchor'),@doc.getCursor('head'))

    # Removes all event listeners from the CodeMirror instance.
    detach: =>
      @doc.off "beforeChange", @onChange

    # Converts a CodeMirror change object into a Operation
    @operationFromCodeMirrorChange: (change, doc) ->
      from = doc.indexFromPos(change.from)
      to   = doc.indexFromPos(change.to)
      length = to - from
      new Operation().retain(from)
                         .delete(length)
                         .insert(change.text.join('\n') )
                         .retain(doc.getValue().length-to) # could be cached

    # Apply an operation to a CodeMirror instance.
    @applyOperationToCodeMirror: (operation, doc) ->
      index = 0 # TODO: Iterate Line/Column based
      for a in operation.actions
        switch Operation.actionType(a)
          when 'retain'
            index += a
          when 'insert'
            doc.replaceRange a, doc.posFromIndex(index)
            index += a.length
          when 'delete'
            from = doc.posFromIndex(index)
            to = doc.posFromIndex(index - a)
            doc.replaceRange "", from, to

    @annotationFromCodeMirrorSelection: (doc,color) ->
      anchor = doc.indexFromPos(doc.getCursor('anchor'))
      head   = doc.indexFromPos(doc.getCursor('head'))

      length = doc.getValue().length # TODO: see above

      if anchor is head
        return new Annotations().plain(anchor)
                                .annotate(0,{'c':['cursor',color]})
                                .plain(length - anchor)
      else if anchor < head
        return new Annotations().plain(anchor)
                                .annotate(head - anchor,{'c':['selection',color]})
                                .annotate(0,{'c':['cursor',color]})
                                .plain(length - head)
      else
        return new Annotations().plain(head)
                                .annotate(0,{'c':['cursor',color]})
                                .annotate(anchor - head,{'c':['selection', color]})
                                .plain(length - anchor)

    registerCallbacks: (cb) =>
      @callbacks = cb

    onChange: (doc, change) =>
      unless @silent
        @trigger "change", CodeMirrorAdapter.operationFromCodeMirrorChange(change, doc)

    onSelectionChange: (cm) =>
      @trigger "annotate", CodeMirrorAdapter.annotationFromCodeMirrorSelection(@doc, @color)

    onGetHelp: (doc, index) =>
      key = "c:" + Math.random().toString(36).substr(2)
      widget = document.createElement("ul")
      widget.className = "autocomplete"
      widget.tabIndex = 1
      console.log angular.element(widget).controller()
      if @autocompletes[this]?
        @autocompletes[this].remove()
      @autocompletes[this] = {
        remove: =>
          try
            angular.element(widget).remove()
          delete @autocompletes[this]
        add: (value) =>
          e = document.createElement("li")
          v = value
          h = value
          if (i = value.indexOf '\t') > 0
            h = value.substr(i + 1)
            v = value.substr(0,i)
          e.innerHTML = h
          e.onclick = ->
            doc.replaceSelection(v)
            doc.setCursor(doc.getCursor())
            doc.getEditor().focus()
          angular.element(e).data("suggest",v)
          angular.element(widget).append(e)
        key: key
      }
      filter = ""
      update = (more) =>
        selected = false
        some = false
        angular.element(widget).children().each (i) ->
          e = angular.element(this)
          e.removeClass("selected")
          if e.data("suggest").indexOf(filter) isnt -1
            e.show()
            some = true
            unless selected
              e.addClass("selected")
            selected = true
          else
            e.hide()
      next = () ->
        cur = angular.element(widget).children(".selected")
        cur.removeClass("selected")
        nxt = cur.nextAll(":not(:hidden)").first()
        if nxt.length > 0
          nxt.addClass("selected").get(0).scrollIntoView()
        else
          angular.element(widget).children(":not(:hidden)").first().addClass("selected").get(0).scrollIntoView()
      prev = () ->
        cur = angular.element(widget).children(".selected")
        cur.removeClass("selected")
        nxt = cur.prevAll(":not(:hidden)").first()
        if nxt.length > 0
          nxt.addClass("selected").get(0).scrollIntoView()
        else
          angular.element(widget).children(":not(:hidden)").last().addClass("selected").get(0).scrollIntoView()
      complete = () =>
        the = angular.element(widget).children(".selected")
        if the.length > 0
          @doc.replaceSelection(the.data("suggest"))
        @autocompletes[this].remove()
        @doc.setCursor(@doc.getCursor())
        @doc.getEditor().focus()
      widget.onkeypress = (e) =>
        filter = filter + String.fromCharCode(e.charCode)
        @doc.replaceSelection(filter)
        #@doc.setCursor(@doc.getCursor())
        update()
        e.preventDefault()
        false
      widget.onkeydown = (e) =>
        switch e.keyCode
          when 8 # backspace
            e.preventDefault()
            if filter.length > 0
              filter = filter.substr(0, filter.length - 1)
              @doc.replaceSelection(filter)
              update(true)
            else
              @doc.getEditor().focus()
          when 13
            complete()
            e.preventDefault()
            false
          when 9
            complete()
            e.preventDefault()
            false
          when 33 # pg up
            for i in [1..10]
              prev()
            e.preventDefault()
          when 34 #pg down
            for i in [1..10]
              next()
            e.preventDefault()
          when 40 #down
            next()
            e.preventDefault()
          when 38 #up
            prev()
            e.preventDefault()
          when 37 #left
            @doc.getEditor().focus()
            @doc.getEditor().execCommand("goCharLeft")
          when 39 #right
            @doc.getEditor().focus()
            @doc.getEditor().execCommand("goCharRight")
          when 27 # esc
            @doc.setCursor(@doc.getCursor())
            @doc.getEditor().focus()
          else
            #@doc.replaceSelection(filter + String.fromCharCode(e.keyCode))
            #@doc.setCursor(@doc.getCursor())
            #@doc.getEditor().focus()
      widget.onblur = =>
        @autocompletes[this]?.remove()
        annotation = new Annotations().plain(@doc.getValue.length)
        @trigger 'annotate', annotation
      doc.getEditor().addWidget(doc.posFromIndex(index), widget, true)
      angular.element(widget).focus()
      annotation = new Annotations().plain(index).annotate(0,{'c': ['cursor',@color],'h': [key]}).plain(doc.getValue().length - index)
      @trigger 'annotate', annotation

    getValue: => @doc.getValue()

    trigger: (event,args...) =>
      action = @callbacks and @callbacks[event]
      action.apply this, args  if action

    applyOperation: (operation) =>
      @silent = true
      cm = @doc.getEditor()
      if cm? then cm.operation =>
        CodeMirrorAdapter.applyOperationToCodeMirror operation, @doc
      else
        CodeMirrorAdapter.applyOperationToCodeMirror operation, @doc
      @silent = false

    annotate: (c,user,name,gutter,output,inline,from,to) =>
      classes = c.c?.join(' ')
      widget = (type,cs,content) ->
        w = angular.element("<#{type} class='#{classes} #{cs}'>#{content}</#{type}>")[0]
        w.title = c.t if c.t
        return w
      line = if to? then to.line else from.line
      if c.e?
        output.push { from: from, to: to or from, type: 'error', content: c.e }
        if inline.errors and cm = @doc.getEditor() then for e in c.e
          @annotations[user.id][name].push cm.addLineWidget line, widget('div','outputWidget error',e)
      if c.w?
        output.push { from: from, to: to or from, type: 'warning', content: c.w }
        if inline.warnings and cm = @doc.getEditor() then for w in c.w
          @annotations[user.id][name].push cm.addLineWidget line, widget('div','outputWidget warning',w)
      if c.i?
        output.push { from: from, to: to or from, type: 'info', content: c.i }
        if inline.output and cm = @doc.getEditor() then for i in c.i
          @annotations[user.id][name].push cm.addLineWidget line, widget('div','outputWidget info',i)
      if c.o?
        output.push { from: from, to: to or from, type: 'info', content: c.o }
        if inline.output and cm = @doc.getEditor() then for i in c.o
          @annotations[user.id][name].push cm.addLineWidget line, widget('div','outputWidget info',i)
      if c.ls?
        gutter.push { line: from.line, type: 'progress', state: c.ls }
      if c.h?
        w = angular.element(document.createElement("div"))
        w.addClass "autocomplete"
        i = document.createElement("input")
        w.append(i)
        l = angular.element(document.createElement("ul"))
        w.append(l)
        i.onkeyup = (e) =>
          if (e.keyCode == 13)
            entry = document.createElement("li")
            entry.innerHTML = i.value
            angular.element(l).append(entry)
            annotation = new Annotations().respond(c.h[0],i.value)
            @trigger 'annotate', annotation
            i.value = ""
        @autocompletes[user.id] = {
          remove: =>
            w.remove()
            delete @autocompletes[user.id]
          add: (value) ->
            entry = if (i = value.indexOf '\t') > 0 then value.substr(i+1) else value
            l.append("<li>#{entry}</li>")
          key: c.h[0]
        }
        @doc.getEditor()?.addWidget(to or from, w[0])
      if classes?
        if to? and c.s?
          marker = @doc.markText from, to,
            replacedWith:      widget('span',classes,c.s)
            handleMouseEvents: true
          @annotations[user.id][name].push marker
        else if to?
          if user.followed
            @doc.getEditor()?.scrollIntoView(from,to)
          marker = @doc.markText from, to,
            className: classes
            title:     c.t
          @annotations[user.id][name].push marker
        else
          if user.followed
            @doc.getEditor()?.scrollIntoView(from)
          bookmark = @doc.setBookmark from,
            widget:     widget('span','','')
            insertLeft: true
          @annotations[user.id][name].push bookmark
      else if c.if
        tooltip = @doc.markText from, to,
          title: c.t
        @annotations[user.id][name].push tooltip

    @registerMouseEvents: (doc) =>

    resetAnnotations: (user, name) => if user?
      @autocompletes[user]?.remove()
      unless @annotations[user]?
        @annotations[user] = {}
      existing = @annotations[user][name]
      if existing?
        for marker in existing
          marker.clear()
      @annotations[user][name] = []

    blur: =>
      annotation = new Annotations().plain(@doc.getValue.length)
      @trigger 'annotate', annotation
      for u, c of @autocompletes
        c.remove()
      @autocompletes = {}

    focus: =>
      console.debug "document focused"

    applyAnnotation: (annotation, user, name, gutter, output, inline) =>
      cm       = @doc.getEditor()

      work = =>
        @resetAnnotations(user.id, name) if user?
        index = 0 # TODO: Iterate Line/Column based with cm.eachLine
        for a in annotation.annotations
          if Annotations.isPlain(a)
            index += a
          else
            from = @doc.posFromIndex(index)
            if a.l > 0
              index += a.l
              to = @doc.posFromIndex(index)
              @annotate(a.c,user,name,gutter,output,inline,from,to)
            else
               @annotate(a.c,user,name,gutter,output,inline,from)

      if cm?
        for response in annotation.responses
          for user, autocomplete of @autocompletes
            if response.r is autocomplete.key
              autocomplete.add(response.a)

      if annotation.annotations.length > 0
        if cm? then cm.operation => work()
        else work()

    updateGutter: (output) => if cm = @doc.getEditor() then cm.operation =>
      cm.clearGutter('progress-gutter')
      for u, c of output
        for n, vs of c
          for v in vs
            if v.type is 'progress'
              span = document.createElement 'div'
              for s in v.state
                span.classList.add("gutter-state-"+s)
              cm.setGutterMarker v.line, 'progress-gutter', span

