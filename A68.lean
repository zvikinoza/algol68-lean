import A68.Syntax
import A68.Lexer
import A68.Parser
import A68.Mode
import A68.Core
import A68.Builtins
import A68.Numfmt
import A68.Blob
import A68.MP
import A68.Elab
import A68.Interp
import A68.Pretty
import A68.Serial
import A68.Runtime
import A68.CodeGen
import A68.Verified.StackMachine
import A68.Verified.Opt
import A68.Verified.Numfmt
import A68.Verified.MP
import A68.Verified.GC

/-!
# a68lean — an Algol 68 compiler written in Lean 4

Root module: importing it elaborates and type checks every part of the
implementation, including the verified components.
-/
