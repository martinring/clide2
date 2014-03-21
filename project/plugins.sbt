logLevel := Level.Warn

resolvers += "Typesafe repository" at "http://repo.typesafe.com/typesafe/releases/"

resolvers += Resolver.url("scala-js-snapshots",
    url("http://repo.scala-js.org/repo/releases/"))(
    Resolver.ivyStylePatterns)

addSbtPlugin("com.typesafe.play" % "sbt-plugin"          % "2.2.1")

addSbtPlugin("com.typesafe.sbt"  % "sbt-native-packager" % "0.7.0-M2")

addSbtPlugin("com.typesafe.sbt"  % "sbt-pgp"             % "0.8.1")

addSbtPlugin("org.scala-lang.modules.scalajs" % "scalajs-sbt-plugin" % "0.4.1")
