logLevel := Level.Warn

resolvers += "Typesafe repository" at "http://repo.typesafe.com/typesafe/releases/"

resolvers += "Typesafe snapshots" at "http://repo.typesafe.com/typesafe/snapshots/"

addSbtPlugin("com.typesafe.play" % "sbt-plugin"          % "2.3.8")

addSbtPlugin("com.typesafe.sbt"  % "sbt-coffeescript"    % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-less"            % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-rjs"             % "1.0.1")

addSbtPlugin("com.typesafe.sbt"  % "sbt-digest"          % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-gzip"            % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-native-packager" % "0.7.0-RC2")

addSbtPlugin("com.typesafe.sbt"  % "sbt-pgp"             % "0.8.2")

addSbtPlugin("org.scala-js" % "sbt-scalajs" % "0.6.1")
