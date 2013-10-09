import sbt._

object Dependencies {
  val slick = "com.typesafe.slick" %% "slick" % "1.0.1"
  val h2    = "com.h2database" % "h2" % "1.3.166"
  val slf4j = "org.slf4j" % "slf4j-nop" % "1.6.4"

  object akka {
    val version = "2.2.1"
    val actor   = "com.typesafe.akka" %% "akka-actor"   % version
    val remote  = "com.typesafe.akka" %% "akka-remote"  % version
    val kernel  = "com.typesafe.akka" %% "akka-kernel"  % version
    val testkit = "com.typesafe.akka" %% "akka-testkit" % version % "test"
  }

  object spray {
    val resolver = "spray" at "http://repo.spray.io/"
    val json = "io.spray" %% "spray-json" % "1.2.5"
  }
  
  object scala {
    val version = "2.10.2"
    val swing   = "org.scala-lang" % "scala-swing"   % version
    val actors  = "org.scala-lang" % "scala-actors"  % version
    val reflect = "org.scala-lang" % "scala-reflect" % version
  }

  object playplugins {
    val slick   = "com.typesafe.play" %% "play-slick"          % "0.5.0.2"
    val mailer  = "com.typesafe"      %% "play-plugins-mailer" % "2.1.0"
  }
}