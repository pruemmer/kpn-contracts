name := "kpn"

version := "0.1"

scalaVersion := "2.11.12"

run / fork := true

Global / cancelable := true

resolvers += "uuverifiers" at "https://eldarica.org/maven/"

//    libraryDependencies += "uuverifiers" %% "princess" % "2021-03-10"
libraryDependencies += "uuverifiers" %% "eldarica" % "nightly-SNAPSHOT"
libraryDependencies   += "org.scalacheck" %% "scalacheck" % "1.14.0" % "test"
