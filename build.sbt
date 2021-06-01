name := "kpn"

version := "0.1"

scalaVersion := "2.11.12"

resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/").withAllowInsecureProtocol(true)

//    libraryDependencies += "uuverifiers" %% "princess" % "2021-03-10"
libraryDependencies += "uuverifiers" %% "eldarica" % "nightly-SNAPSHOT"
