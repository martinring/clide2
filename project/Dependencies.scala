import sbt._

object Dependencies {
  val slick = "com.typesafe.slick" %% "slick" % "1.0.1"

  object akka {
    val version = "2.2.0"
    val actor   = "com.typesafe.akka" %% "akka-actor"   % version
    val remote  = "com.typesafe.akka" %% "akka-remote"  % version
    val kernel  = "com.typesafe.akka" %% "akka-kernel"  % version
    val testkit = "com.typesafe.akka" %% "akka-testkit" % version % "test"
  }

  object atmos {
    val trace = "com.typesafe.atmos" % "trace-akka-2.2.1_2.10" % "1.3.0"
  }

  object scala {
    val version = "2.10.2"
    val swing   = "org.scala-lang" % "scala-swing"  % version
    val actors  = "org.scala-lang" % "scala-actors" % version
  }

  object playplugins {
    val slick   = "com.typesafe.play" %% "play-slick"          % "0.5.0.2"
    val mailer  = "com.typesafe"      %% "play-plugins-mailer" % "2.1.0"
  }
}