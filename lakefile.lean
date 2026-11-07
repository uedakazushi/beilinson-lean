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

/-- Build the Verso HTML and a single printable PDF as part of plain 'lake build'. -/
@[default_target]
target book_formats pkg : Unit := do
  let _ ← «generate-book».fetch
  let exe := pkg.buildDir / "bin" / "generate-book"
  let html ← IO.Process.output { cmd := exe.toString }
  if html.exitCode != 0 then
    error s!"Verso HTML generation failed:\n{html.stderr}\n{html.stdout}"
  let pdf ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/build_pdf.py"]
  }
  if pdf.exitCode != 0 then
    error s!"PDF generation failed:\n{pdf.stderr}\n{pdf.stdout}"
  logInfo "HTML: _out/html/index.html; PDF: _out/beilinson-book.pdf"
  return .nil
