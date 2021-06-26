
lazy val `main` = project.in(file("src-main")).settings(
  sharedSettings,
  libraryDependencies ++= Seq(
    //parsing
    "com.github.molikto" % "scala-parser-combinators-dotty" % "0.1",
    // platform
    "org.ow2.asm" % "asm" % "9.2",
    "org.ow2.asm" % "asm-util" % "9.2",
    "org.ow2.asm" % "asm-tree" % "9.2",
    // utils
    ("com.lihaoyi" %% "fansi" % "0.2.14").withDottyCompat(scalaVersion.value),
  ),
  javaOptions += "-Xss1G",
  fork in run := true,
  baseDirectory in run := file("."),
)


val sharedSettings = Seq(
  scalaVersion := "0.20.0-RC1",
  resolvers ++= Seq(
    "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/",
    Resolver.jcenterRepo,
    Resolver.sonatypeRepo("releases"),
    "jitpack" at "https://jitpack.io" // this is for the custom built parser combinator library
  ),
  sources in (Compile, doc) := Seq.empty,
  publishArtifact in (Compile, packageDoc) := false,
  javacOptions ++= Seq(
    "-Xdiags:verbose"
  ),
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

