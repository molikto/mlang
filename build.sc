// build.sc
import mill._, scalalib._


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
  def ivyDeps = Agg(
    ivy"scala-parser-combinators-dotty::scala-parser-combinators-dotty:0.1.0",
    // platform
    ivy"org.ow2.asm:asm:7.2",
    ivy"org.ow2.asm:asm-util:7.2",
    ivy"org.ow2.asm:asm-tree:7.2",
    ivy"com.lihaoyi::fansi:0.2.7".withDottyCompat(scalaVersion())
  )
}