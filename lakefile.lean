import Lake
open Lake DSL System

package algol68 where
  version := v!"0.2.0"

/-- Default definitions of the two hooks that compiled programs override.
    They are linked into the `a68lean` executable only; a compiled program
    provides its own and links just the Lean library. -/
target stubs.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "stubs.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "stubs.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile srcJob flags

/-- Operating-system services of the standard environment (processes, pipes, directories,
    time, regular expressions), linked into `a68lean` and into compiled programs alike. -/
target sys.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "sys.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "sys.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile srcJob flags

/-- The C runtime of compiled programs: their values, frames and operand stack in C memory
    (docs/GC-DESIGN.md).  Linked into compiled programs; the interpreter links stubs for the
    few entry points the Lean side calls. -/
target rt.o pkg : FilePath := do
  let oFile := pkg.buildDir / "csrc" / "rt.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "rt.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile srcJob flags

extern_lib liba68stubs pkg := do
  let name := nameToStaticLib "a68stubs"
  let job ← fetch <| pkg.target ``stubs.o
  let sysJob ← fetch <| pkg.target ``sys.o
  let rtJob ← fetch <| pkg.target ``rt.o
  buildStaticLib (pkg.staticLibDir / name) #[job, sysJob, rtJob]

@[default_target]
lean_lib A68 where
  roots := #[`A68]
  -- compiled programs link the static archive, so build it by default
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe a68lean where
  root := `Main
