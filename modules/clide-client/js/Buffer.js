{
  window.Buffer = {
    apply: function() {
      var underlying = arguments
      return {
        apply:  function(idx) { return underlying[idx] },
        update: function(idx, elem) { underlying[idx] = elem }
        length: function() { return underlying.length }
        clear:  function() { return underlying.splice(0) }
        "+=": function(elem) {  return Buffer.apply(underlying) }
      }
    }
  }
}
