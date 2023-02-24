val scala3Version = "3.2.2"

lazy val root = project
  .in(file("."))
  .settings(
    name := "yoneda",
    version := "1.0.0",

    scalaVersion := scala3Version,

  )
