import Lake
open Lake DSL System

package algol68 where
  version := v!"0.2.0"

/-- The C runtime of compiled programs, plain C (docs/GC-DESIGN.md, docs/ARCHITECTURE.md):
    values, frames and the collector (rt.c), the tables of a program, transput and the
    prelude, the general operators, number formatting, multi-precision arithmetic and the
    operating-system services.  A compiled program links this archive and the C library
    only; the `a68lean` executable links it too, for the services the evaluator shares. -/
def rtSources : Array String :=
  #["rt", "tables", "io", "prelude", "ops", "os", "fmt", "bigint", "mp", "mpmath", "mpfmt", "mprt"]

extern_lib liba68rt pkg := do
  let name := nameToStaticLib "a68rt"
  let mut jobs := #[]
  for n in rtSources do
    let oFile := pkg.buildDir / "csrc" / (n ++ ".o")
    let srcJob ← inputTextFile <| pkg.dir / "csrc" / (n ++ ".c")
    jobs := jobs.push (← buildO oFile srcJob #["-fPIC", "-O2", "-ffp-contract=off"])
  buildStaticLib (pkg.staticLibDir / name) jobs

/-- The evaluator's side of the C code: the `@[extern]` wrappers of the operating-system
    services (sys.c) and the hooks compiled programs supply (stubs.c).  Linked into
    `a68lean` only. -/
def stubSources : Array String := #["stubs", "sys"]

extern_lib liba68stubs pkg := do
  let name := nameToStaticLib "a68stubs"
  let mut jobs := #[]
  for n in stubSources do
    let oFile := pkg.buildDir / "csrc" / (n ++ ".o")
    let srcJob ← inputTextFile <| pkg.dir / "csrc" / (n ++ ".c")
    jobs := jobs.push (← buildO oFile srcJob #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"])
  buildStaticLib (pkg.staticLibDir / name) jobs

@[default_target]
lean_lib A68 where
  roots := #[`A68]
  -- compiled programs link the static archive, so build it by default
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe a68lean where
  root := `Main
