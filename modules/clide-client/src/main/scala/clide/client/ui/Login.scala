package clide.client.ui

import clide.reactive.ui._
import clide.reactive.ui.html.HTML5._

@view class Login {
  html"""
    <div>
    <Dialog>
      <div class='row'>        
			  <div class="col-sm-5 col-sm-offset-1 col-lg-4 col-lg-offset-2">
			      <h2 title="version 2.0-SNAPSHOT">Welcome to clide</h2>
			      <p>
			        Please enter your credentials
			      </p>
			      <form name="loginForm" role="form" class="ng-pristine ng-invalid ng-invalid-required">
			        <p class="text-danger"></p>
			        <div class="form-group">
			          <span class="text-danger pull-right"></span>
			          <input class="form-control" type="text" name="username" id="username" placeholder="username" required="${true}" autofocus="${true}"/>
			        </div>
			        <div class="form-group">
			          <span class="text-danger pull-right ng-binding ng-hide"></span>
			          <input class="form-control ng-pristine ng-invalid ng-invalid-required" type="password" id="password" name="password" placeholder="password" required="${true}"/>
			        </div>
			        <label for="staySignedIn" class="checkbox-inline">
			          <span class="icons">
			            <span class="first-icon fui-checkbox-unchecked"></span>
			            <span class="second-icon fui-checkbox-checked"></span>
			          </span>
			          <input type="checkbox" name="staySignedIn" disabled="${false}" id="staySignedIn" class="ng-pristine ng-valid"/> keep me signed in
			        </label>
			        <div class="pull-right">
			          <a class="btn btn-link" href="/signup">Sign Up</a>
			          <button type="submit" class="btn btn-primary">
			            <i class="fa fa-sign-in"></i> Login
			          </button>
			        </div>
			      </form>
			      <div class="clearfix"></div>
			    </div>        
        <div class='col-sm-5 col-lg-4'>
        </div>
      </div>
      <div class='row'>
        <div class='col-sm-10 col-sm-offset-1 col-lg-8 col-lg-offset-2 text-right'>
          <small class='text-muted'>
            © 2012-2013 Martin Ring - Licensed under LGPL v3 - You're looking at version 2.0-SNAPSHOT. Last updated 3/20/2014.
          </small>
        </div>
      </div>
    </Dialog>
    </div>
  """
}