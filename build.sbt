lazy val trajan = slangEmbeddedProject("TrajanSlang")

val scalaVer = "2.12.9"

val sireumScalacVersion = "4.20190806.50272f6"

val runtimeVersion = "51ee010f73"

val commonSettings = Seq(
  organization := "org.sireum",
  incOptions := incOptions.value.withLogRecompileOnMacro(false),
  scalaVersion := scalaVer,
  scalacOptions := Seq("-target:jvm-1.8", "-deprecation",
    "-Ydelambdafy:method", "-feature", "-unchecked", "-Xfatal-warnings"),
  Test / parallelExecution := true,
  resolvers ++= Seq(Resolver.sonatypeRepo("public"), "jitpack" at "https://jitpack.io"),
  addCompilerPlugin("org.sireum" %% "scalac-plugin" % sireumScalacVersion),
  libraryDependencies ++= Seq(
    "org.sireum.runtime" %% "library" % runtimeVersion,
    "org.scalatest" %% "scalatest" % "3.0.8" % "test"
  )
)

def slangEmbeddedProject(projId: String) =
  Project(id = projId, base = file(projId)).settings(commonSettings)
