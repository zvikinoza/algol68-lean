# Architecture

`a68lean` is organised as a classical compiler front end followed by an
evaluator for the compiled representation. Every stage is a total Lean
function except where noted.

```
source text
   │  A68.Lexer.lex                (total: recursion on remaining input)
   ▼
tokens ──► A68.Parser.prescan      (collects MODE / OP / PRIO names and priorities)
   │  A68.Parser.parse             (recursive descent, backtracking where Algol 68 needs it)
   ▼
A68.Syntax  (parse tree)
   │  A68.Elab.elabProgram         (modes, coercions, operator identification, scopes)
   ▼
A68.Core    (typed core representation with explicit coercions and resolved names)
   │  A68.Interp.run
   ▼
observable behaviour (stdout bytes, files, exit status)
```

## Lexer (`A68/Lexer.lean`)

The tokeniser handles a68g's upper-stropping conventions. Two decisions matter
for compatibility:

* Tags may contain spaces: `new line` and `newline` are the same identifier.
  The lexer joins a tag across spaces when the next character can continue a
  tag; `FOR i TO n DO` still splits correctly because bold words cannot
  continue a tag.
* Operator symbols follow a68g's scanner exactly: an operator is a *monad*
  (`% ^ & + - ~ ! ?`) or *nomad* (`> < / = *`) character, optionally followed
  by one nomad, then optionally `=`, `:`, `=` (in that order). Consequently
  `x:=-1` lexes as `x := -1`, `2**-1` as `2 ** -1`, and `+:=`, `<<:=`, `=:=`
  are single operator symbols.

Comments and pragmats are consumed by the lexer; pragmats are kept as tokens
so that `precision`, `echo` and `regression` can be honoured.

## Parser (`A68/Parser.lean`)

Algol 68 cannot be parsed without knowing which bold words are mode indicants
and which are operators, and with what priority. `prescan` walks the token
stream once, tracking bracket depth, and records every `MODE`, `OP` and `PRIO`
declaration. The parser proper is recursive descent with precedence climbing
for formulas (all dyadic operators are left associative; monadic operators
bind tightest, so `-2**2 = 4` as in a68g).

Constructs that need lookahead beyond one token — routine texts, conformity
alternatives, declarations versus casts, enquiry clauses versus collaterals —
are recognised by speculative parsing that backtracks on failure. Once a
routine header or a `declarer identifier` prefix has been seen the parser
commits, so that errors inside the body are reported rather than swallowed.

The parser is the one component written with `partial def` (termination of
a backtracking parser is not worth proving); it is nevertheless total in
practice because every alternative consumes input or fails.

## Modes (`A68/Mode.lean`)

Modes are a first-order type: `int n`, `real n` (with the `LONG` level `n`),
`ref`, `row dims flex`, `proc`, `struct`, `union`, and `named` for mode
indicants. Recursive modes (`MODE NODE = STRUCT (INT v, REF NODE next)`) stay
as `named` references into a table; equivalence (`Mode.eqv`) unfolds them
with a fuel bound, ignores the `FLEX` flag (which only affects assignment), and
compares structurally.

## Elaboration (`A68/Elab.lean`)

The elaborator implements the Revised Report's coercion discipline. Every unit
is elaborated in a *context*:

| context | permitted coercions |
|---|---|
| strong (target mode known) | deproceduring, dereferencing, uniting, widening, rowing, voiding |
| firm (operands) | deproceduring, dereferencing, uniting |
| meek (conditions, subscripts, calls) | deproceduring, dereferencing |
| weak (slices, selections) | dereferencing down to a name of a row/struct |
| soft (assignment destinations) | deproceduring |

`coerce` searches for a coercion sequence and returns the core term with the
coercions made explicit (`deref`, `deproc`, `widen`, `rowOf`, `unite`,
`voiding`). Balancing (`balance`) chooses a common mode for the branches of
conditional and case clauses when no target mode is known; branches that never
yield a value (`stop`, jumps) do not take part.

Operator identification searches user-declared operators innermost-scope-first
with firm coercions of the operands, then falls back to the standard prelude,
where a68g's widening of mixed `INT`/`REAL`/`LONG` operands is applied.

Name resolution assigns every declared object a `(frame depth, slot)` pair.
Every serial clause, routine text, loop and conformity alternative opens a
frame, and the evaluator pushes a frame at exactly the same points, so the
static depth computed here equals the dynamic environment depth. Enquiry
clauses (`IF INT c = …; c > 0 THEN … c … FI`) keep their frame alive for the
branches, as the language requires.

## Core representation (`A68/Core.lean`)

`Core` is a small language: literals, cell loads and name creation
(`loadCell`, `refCell`), explicit coercions, assignment, identity relation,
builtin operators tagged with their operand modes, calls, routine texts,
slices, selections, row creation, generators, blocks with label tables,
collaterals, conditionals, cases, loops, jumps, short-circuit operators and
format texts. Values (`Value`) are immutable data: integers (unbounded `Int`,
range-checked per mode), floats, booleans, byte characters, bits, rows (bounds
plus a flat element array), structs, united values (tagged with their
constituent mode), names (`ref cell path`), closures, formats and files.

## Evaluator (`A68/Interp.lean`)

The runtime keeps a heap of *cells* (`Array Value`); a name is a cell number
plus a path of selections (field, element, or a trimmed sub-row view). Because
values are immutable, assignment through a name is a functional update along
the path; the value is detached from its cell first so that Lean's runtime
performs the update in place when the value is not shared, which keeps
element-wise array filling linear.

Environments are lists of frames; closures capture the environment at routine
text evaluation. Control flow that leaves an expression (jumps, `stop`, run
time errors, mended file ends) is an `ExceptT` exception caught by the
enclosing block or loop.

Numeric semantics mirror a68g: `INT` is 32-bit with overflow detection on every
operation, `LONG INT`/`LONG LONG INT` have 49 and 84 decimal digits (or the
`PR precision` value), `REAL` operations raise a runtime error on infinities
and NaNs, `REAL ** INT` is square-and-multiply in a68g's order, and
`REAL ** REAL` is `exp (y · ln x)`.

Transput lives in the same module: unformatted `print`/`put`, the formatted
`printf`/`putf` picture machine (frames, moulds, sign shifting, zero
suppression, replicated collections, embedded formats, column alignment),
`read`/`get`/`getf`, and files (disk files, string-associated files, standard
streams, logical-file-end and value-error menders).

## Number formatting (`A68/Numfmt.lean`)

All conversions go through an exact decimal type `Dec = mant × 10^exp` and
follow a68g's algorithms step by step (`whole`, `fixed`, `float` and its
helpers `sub_fixed`, `standardize`). The only inexact step in a68g is the
conversion of a C `double` into its multi-precision representation, which
extracts 21 significant digits with a floating-point loop; `realToDec`
reproduces that loop bit for bit (including a68g's `ten_up` power table), so
that outputs such as `123456789012345671.653` for the double
`123456789012345678.0` are identical. See
[COMPATIBILITY.md](COMPATIBILITY.md) for details.
