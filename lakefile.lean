import Lake
open System Lake DSL

package splitmix

input_file splitmix.c where
  path := "c" / "splitmix.c"
  text := true

target splitmix.o pkg : FilePath := do
  let srcJob ← splitmix.c.fetch
  let oFile := pkg.buildDir / "c" / "splitmix.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O3"] "cc" getLeanTrace

target libsplitmix pkg : FilePath := do
  let o ← splitmix.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "splitmix") #[o]

@[default_target]
lean_lib SplitMix

/-- The module with the `@[extern]` declarations, compiled to a shared
library so `#eval` can call the C code. Lake assigns a module to the *last*
library that claims it, so this must stay below `SplitMix`. -/
lean_lib SplitMixFFI where
  roots := #[`SplitMix.Native]
  precompileModules := true
  moreLinkObjs := #[libsplitmix]

/-- Test-only modules. -/
lean_lib Tests where
  srcDir := "test"

@[test_driver]
lean_exe tests where
  srcDir := "test"
  root := `Main

lean_exe bench where
  srcDir := "bench"
  root := `Bench
