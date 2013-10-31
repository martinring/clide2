 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors

import akka.actor._
import clide.models._
import clide.Core.DB
import clide.Core.DAL._
import slick.session.Session

/**
 * 
 * @author Martin Ring <martin.ring@dfki.de>
 */
object UserServer {
  private[clide] def apply() = Props[UserServer]
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class UserServer extends Actor with ActorLogging {
  import Messages.internal._
  import Messages._
  import Events._
  
  var users: Seq[UserInfo with Password] = Seq.empty
  
  def receive = {    
    case SignUp(name,email,password) =>
      log.info("attempting to sign up")
      val user = UserInfo(name,email).withPassword(password)      
      DB.withSession { implicit s: Session =>
        if (UserInfos.get(user.name).isDefined) {
          sender ! ActionFailed(Map("name" -> "this name is already registered"))
        } else if (UserInfos.getByEmail(user.email).isDefined) {
          sender ! ActionFailed(Map("email" -> "this email is already registered"))
        }
        else {
          UserInfos.insert(user) 
          context.actorOf(UserActor(user), user.name)
	      sender ! SignedUp(user)
	      context.system.eventStream.publish(SignedUp(user))
        }        
      }
      
    case IdentifiedFor(name,key,message) =>
      context.child(name) match {
        case None      => sender ! DoesntExist
        case Some(ref) => 
          log.info(f"identified forward to $name: $message")
          ref.forward(Identified(key,message))
      }
      
    case AnonymousFor(name,message) =>
      context.child(name) match {
        case None => sender ! DoesntExist
        case Some(ref) => 
          log.info(f"anonymous forward to $name: $message")
          ref.forward(Anonymous(message))
      }
  }
  
  override def preStart() {
    log.info("creating user actors")
    DB.withSession { implicit session: Session => 
      users = UserInfos.getAll.toList      
    }
    users.foreach { user => context.actorOf(UserActor(user), user.name) }
    log.info("waiting for requests")
  }
}