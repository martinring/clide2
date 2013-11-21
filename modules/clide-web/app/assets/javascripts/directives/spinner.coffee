##             _ _     _                                                      ##
##            | (_)   | |                                                     ##
##         ___| |_  __| | ___      clide 2                                    ##
##        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  ##
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

define -> () ->
  restrict: 'E'
  template: """
<div class="outerSpinnerContainer">
<div class="innerSpinnerContainer">
<div class="spinner">
<div class="wBall" id="wBall_1">
<div class="wInnerBall">
</div>
</div>
<div class="wBall" id="wBall_2">
<div class="wInnerBall">
</div>
</div>
<div class="wBall" id="wBall_3">
<div class="wInnerBall">
</div>
</div>
<div class="wBall" id="wBall_4">
<div class="wInnerBall">
</div>
</div>
<div class="wBall" id="wBall_5">
<div class="wInnerBall">
</div>
</div>
</div>
</div>
</div>
"""

  replace: true
