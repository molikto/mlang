name := "mlang"

version := "0.1"

scalaVersion := "2.12.8"


libraryDependencies += "com.lihaoyi" %% "acyclic" % "0.1.7" % "provided"

autoCompilerPlugins := true

addCompilerPlugin("com.lihaoyi" %% "acyclic" % "0.1.7")


scalacOptions += "-P:acyclic:force"

libraryDependencies ++= Seq(
  "com.twitter" %% "util-eval" % "6.43.0"
)

