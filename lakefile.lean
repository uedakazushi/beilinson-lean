import Lake
open Lake DSL

package «beilinson-lean» where
  version := v!"0.2.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

require verso from git
  "https://github.com/leanprover/verso" @ "v4.35.0"

@[default_target]
lean_lib Beilinson

@[default_target]
lean_lib Book

lean_exe «generate-book» where
  root := `Main

/--
Build both the Verso HTML and the native TeX → LuaLaTeX PDF output.
The executable must be built before the script is run.
-/
@[default_target]
target book_formats : Unit := do
  let exeJob ← «generate-book».fetch
  exeJob.mapM fun executable => do
    proc {
      cmd := "bash"
      args := #["scripts/build_book.sh", executable.toString]
    }
