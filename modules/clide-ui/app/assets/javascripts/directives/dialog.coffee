### @directive directives:dialog ###
define -> () -> 
  restrict: 'E'
  transclude: true
  replace: true
  template: """
<div class='dialogOuterContainer'>
  <div class='dialogInnerContainer'>
    <div class='dialog'>
      <div class='container' ng-transclude>
      </div>
    </div>
  </div>
</div>"""