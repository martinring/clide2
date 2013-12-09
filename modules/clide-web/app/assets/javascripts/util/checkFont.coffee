###
# Checks if a font is available to be used on a web page.
#
# @param {String} fontName The name of the font to check
# @return {Boolean}
# @license MIT
# @copyright Sam Clarke 2013
# @author Sam Clarke <sam@samclarke.com>
#
# Adapted to coffeescript/requirejs and simplified by Martin Ring
###
define ->
  container = document.createElement("span")
  container.style.position = 'absolute'
  container.style.fontSize = '128px'
  container.style.left     = '-99999px'
  container.innerHTML = Array(100).join("wi")

  calculateWidth = (fontFamily) ->
    container.style.fontFamily = fontFamily
    document.body.appendChild container
    width = container.clientWidth
    document.body.removeChild container
    width

  monoWidth  = calculateWidth("monospace")
  sansWidth  = calculateWidth("sans-serif")

  if monoWidth is sansWidth
    console.warn('monospace and sans-serif widths are the same. checkFont will not be reliable!')

  return (fontName) ->
    monoWidth isnt calculateWidth("#{fontName}, monospace") or
    sansWidth isnt calculateWidth("#{fontName}, sans-serif")
