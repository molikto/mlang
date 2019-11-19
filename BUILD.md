# Build

the project is written in Scala (it use [Dotty](http://dotty.epfl.ch/), future Scala 3) and is a standard SBT project. ~~it can be cross compiled to Scala.js and Scala JVM. currently we are only compiling on JVM.~~

to compile use ~~`sbt mainJVM/compile`~~ `sbt main/compile`

to typecheck the standard library, run ~~`sbt mainJVM/run`~~ `sbt main/run`

~~the project can be imported into IntelliJ IDEA, and to run/debug, just setup a profile to run `mlang.poorparser.Main` with classpath of module `jvm-main`. currently you also need to add vm options `-Xss1G`~~

~~if you have trouble compiling inside IntelliJ IDEA (because it has bad cross platform compilation support), you can setup a terminal compile watch with `sbt` then inside it `~mainJVM/compile`, and disable compilation in IntelliJ IDEA's run target.~~

Dotty lacks IntelliJ IDEA support now, so you need to use VS Code as IDE: run `sbt launchIDE`

# Edit mlang code

we currently have a `.poor` syntax (because we want a better syntax: a structural editor). it uses some wired unicode characters, so to write library code, import `settings.zip` to IntelliJ IDEA, it defines some "Live Templates", or key shortcuts to input certain characters

thanks to [@ice1000](https://github.com/ice1000), we have syntax highlighting for `.poor` files in IntellIJ IDEA, install this plugin: https://github.com/owo-lang/intellij-dtlc

