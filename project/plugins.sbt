logLevel := Level.Warn

resolvers += "Typesafe repository" at "http://repo.typesafe.com/typesafe/releases/"

addSbtPlugin("com.typesafe.play" % "sbt-plugin"      % "2.2.0")

addSbtPlugin("com.typesafe.akka" % "akka-sbt-plugin" % "2.2.1")

addSbtPlugin("com.typesafe.sbt"  % "sbt-atmos"       % "0.3.1")

addSbtPlugin("com.typesafe.sbt"  % "sbt-atmos-play"  % "0.3.1")