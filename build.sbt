

lazy val sharedSettings: Seq[Def.Setting[_]] = Seq(
  name := "mlang",
  version := "0.1",
  scalaVersion := "0.13.0-RC1",
  libraryDependencies ++= Seq(
    "com.novocode" % "junit-interface" % "0.11" % "test"
  ),
)


lazy val mlang = project
    .in(file("mlang"))
    .settings(sharedSettings: _*)
    // .settings(
    //   libraryDependencies +=
    // )

lazy val `mlang-imgui` = project
    .in(file("mlang-imgui"))
    .settings(sharedSettings: _*)
    .settings(
      libraryDependencies += "org.ice1000.jimgui" % "core" % "v0.6"
    ).dependsOn(mlang)

//libraryDependencies += "com.lihaoyi" %% "acyclic" % "0.1.7" % "provided"
//
//autoCompilerPlugins := true
//
//addCompilerPlugin("com.lihaoyi" %% "acyclic" % "0.1.7")
//
//scalacOptions += "-P:acyclic:force"

// libraryDependencies ++= Seq(
//   "com.twitter" %% "util-eval" % "6.43.0",
//   "com.lihaoyi" %% "utest" % "0.6.6" % "test"
// )

// testFrameworks += new TestFramework("utest.runner.Framework")


