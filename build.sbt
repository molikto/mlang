
lazy val `main` = project.in(file("src-main")).settings(
  sharedSettings,
  libraryDependencies ++= Seq(
    ("com.lihaoyi" %% "fansi" % "0.2.7").withDottyCompat(scalaVersion.value),
    "ch.epfl.lamp" %% "dotty-staging" % scalaVersion.value,
    "scala-parser-combinators-dotty" %% "scala-parser-combinators-dotty" % "0.1.0",
    "net.bytebuddy" % "byte-buddy" % "1.10.2"
  )
)


val sharedSettings = Seq(
  scalaVersion := "0.20.0-RC1",
  resolvers ++= Seq(
    "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/",
    Resolver.jcenterRepo,
    Resolver.sonatypeRepo("releases"),
  ),
  sources in (Compile, doc) := Seq.empty,
  publishArtifact in (Compile, packageDoc) := false,
  scalacOptions ++= Seq(
    "-language:implicitConversions",
    "-deprecation", // Emit warning and location for usages of deprecated APIs.
    "-feature", // Emit warning and location for usages of features that should be imported explicitly.
    "-unchecked", // Enable additional warnings where generated code depends on assumptions.
    "-Yoverride-vars",
    //"-P:acyclic:force",
  ),
//  autoCompilerPlugins := true,
//  addCompilerPlugin("com.lihaoyi" %% "acyclic" %  "0.2.0"),
//  libraryDependencies += "com.lihaoyi" %% "acyclic" % "0.2.0" % "provided",
)

