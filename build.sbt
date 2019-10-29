import sbtcrossproject.CrossPlugin.autoImport.{crossProject, CrossType}




lazy val `main` = crossProject(JSPlatform, JVMPlatform).in(file("src-main")).settings(
  sharedSettings,
  libraryDependencies ++= Seq(
    "org.scala-lang.modules" %%% "scala-parser-combinators" % "1.1.2" ,
    "com.lihaoyi" %%% "fansi" % "0.2.7"
  ),
).jsConfigure(_.enablePlugins(ScalaJSPlugin)).jvmConfigure(_.settings(
  libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % scalaVersion.value
  )
))

lazy val `editor-web` = project.in(file("src-editor-web")).settings(
  sharedSettings,
  scalaJSUseMainModuleInitializer := true,
  libraryDependencies ++= Seq(
    "org.scala-js" %%% "scalajs-dom" % "0.9.7",
    "com.lihaoyi" %%% "scalatags" % "0.7.0"
  )
).enablePlugins(ScalaJSPlugin).dependsOn(`main`.js)

val sharedSettings = Seq(
  scalaVersion := "2.13.1",
  resolvers ++= Seq(
    "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/",
    Resolver.jcenterRepo,
    Resolver.sonatypeRepo("releases"),
  ),
  sources in (Compile, doc) := Seq.empty,
  publishArtifact in (Compile, packageDoc) := false,
  testFrameworks += new TestFramework("utest.runner.Framework"),
  scalacOptions ++= Seq(
    "-language:implicitConversions",
    "-deprecation", // Emit warning and location for usages of deprecated APIs.
    "-feature", // Emit warning and location for usages of features that should be imported explicitly.
    "-unchecked", // Enable additional warnings where generated code depends on assumptions.
    //"-Xfatal-warnings", // Fail the compilation if there are any warnings.
    //"-Xlint", // Enable recommended additional warnings.
    //"-Ywarn-adapted-args", // Warn if an argument list is modified to match the receiver.
    "-Ywarn-dead-code", // Warn when dead code is identified.
    "-Ywarn-numeric-widen", // Warn when numerics are widened.
    "-Xlint:-unused,_",
    "-P:acyclic:force",
  ),
  autoCompilerPlugins := true,
  addCompilerPlugin("com.lihaoyi" %% "acyclic" %  "0.2.0"),
  libraryDependencies += "com.lihaoyi" %% "acyclic" % "0.2.0" % "provided",
)

