// build.sc
import mill._, scalalib._

import coursier.maven.MavenRepository


trait MlangModule extends SbtModule {
  def scalaVersion = "0.20.0-RC1"
  def scalacOptions = Seq(
    "-language:implicitConversions",
    "-deprecation", // Emit warning and location for usages of deprecated APIs.
    "-feature", // Emit warning and location for usages of features that should be imported explicitly.
    "-unchecked", // Enable additional warnings where generated code depends on assumptions.
    "-Yoverride-vars",
  )
}
object main extends MlangModule {
  def millSourcePath = os.pwd / "src-main"
  def repositories = super.repositories ++ Seq(
    MavenRepository("https://jitpack.io")
  )
  def ivyDeps = Agg(
    ivy"com.github.molikto::scala-parser-combinators-dotty:0.2",
    // platform
    ivy"org.ow2.asm:asm:8.0.1",
    ivy"org.ow2.asm:asm-util:8.0.1",
    ivy"org.ow2.asm:asm-tree:8.0.1",
    ivy"com.lihaoyi::fansi:0.2.9".withDottyCompat(scalaVersion())
  )
}