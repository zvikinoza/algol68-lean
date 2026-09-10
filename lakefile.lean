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

extern_lib liba68stubs pkg := do
  let name := nameToStaticLib "a68stubs"
  let job ← fetch <| pkg.target ``stubs.o
  buildStaticLib (pkg.staticLibDir / name) #[job]

@[default_target]
lean_lib A68 where
  roots := #[`A68]
  -- compiled programs link the static archive, so build it by default
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe a68lean where
  root := `Main
