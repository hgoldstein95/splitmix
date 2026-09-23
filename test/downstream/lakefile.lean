import Lake
open Lake DSL

/-! A stand-in for a package that depends on splitmix. `lake build` here
checks that `#eval` of the native functions works across package
boundaries, and that executables link the C code. -/

package downstream

require splitmix from "../.."

@[default_target]
lean_lib Downstream

@[default_target]
lean_exe downstream where
  root := `Main
