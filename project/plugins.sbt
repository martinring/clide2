logLevel := Level.Warn

resolvers += "Typesafe repository" at "http://repo.typesafe.com/typesafe/releases/"

resolvers += "Typesafe snapshots" at "http://repo.typesafe.com/typesafe/snapshots/"

resolvers += Resolver.url("scala-js-snapshots",
    url("http://repo.scala-js.org/repo/snapshots/"))(Resolver.ivyStylePatterns)

resolvers += Resolver.url("scala-js-releases",
    url("http://dl.bintray.com/content/scala-js/scala-js-releases"))(
    Resolver.ivyStylePatterns)

addSbtPlugin("com.typesafe.play" % "sbt-plugin"          % "2.3.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-coffeescript"    % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-less"            % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-rjs"             % "1.0.1")

addSbtPlugin("com.typesafe.sbt"  % "sbt-digest"          % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-gzip"            % "1.0.0")

addSbtPlugin("com.typesafe.sbt"  % "sbt-native-packager" % "0.7.0-RC2")

addSbtPlugin("com.typesafe.sbt"  % "sbt-pgp"             % "0.8.2")

addSbtPlugin("org.scala-lang.modules.scalajs" % "scalajs-sbt-plugin" % "0.5.0")
