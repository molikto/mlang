lazy val sharedSettings: Seq[Def.Setting[_]] = Seq(
  version := "0.1",
  scalaVersion := "0.13.0-RC1",
  resolvers += Resolver.jcenterRepo,
  libraryDependencies ++= Seq(
    "com.novocode" % "junit-interface" % "0.11" % "test"
  ),
)

lazy val mlang = project
    .in(file("mlang"))
    .settings(sharedSettings: _*)

lazy val `mlang-swing` = project
    .in(file("mlang-swing"))
    .settings(sharedSettings: _*)
    .settings(
      libraryDependencies ++= Seq(
      )
    ).dependsOn(mlang)

lazy val `mlang-imgui` = project
    .in(file("mlang-imgui"))
    .settings(sharedSettings: _*)
    .settings(
      libraryDependencies ++= Seq(
        "org.ice1000.jimgui" % "core" % "v0.7"
      )
    ).dependsOn(mlang)
