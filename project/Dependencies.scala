object Dependencies {
  val slick = "com.typesafe.slick" %% "slick" % "1.0.1"

  object akka {
    val version = "2.2.0"
    val actor = "com.typesafe.akka"   %% "akka-actor"   % version
    val remote = "com.typesafe.akka"  %% "akka-remote"  % version
    val testkit = "com.typesafe.akka" %% "akka-testkit" % version % "test"
  }

  object scala {
    val version = "2.10.2"
    val swing  = "org.scala-lang" % "scala-swing"  % version,
    val actors = "org.scala-lang" % "scala-actors" % version
  }
}